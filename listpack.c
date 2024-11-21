/* Listpack -- A lists of strings serialization format
 *
 * This file implements the specification you can find at:
 *
 *  https://github.com/antirez/listpack
 *
 * Copyright (c) 2017, Salvatore Sanfilippo <antirez at gmail dot com>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *   * Redistributions of source code must retain the above copyright notice,
 *     this list of conditions and the following disclaimer.
 *   * Redistributions in binary form must reproduce the above copyright
 *     notice, this list of conditions and the following disclaimer in the
 *     documentation and/or other materials provided with the distribution.
 *   * Neither the name of Redis nor the names of its contributors may be used
 *     to endorse or promote products derived from this software without
 *     specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

#include "listpack.h"
#include "listpack_malloc.h"

#define LP_HDR_SIZE 6 /* 32 bit total len + 16 bit number of elements. */
#define LP_HDR_NUMELE_UNKNOWN UINT16_MAX
#define LP_MAX_INT_ENCODING_LEN 9
#define LP_MAX_BACKLEN_SIZE 5
#define LP_MAX_ENTRY_BACKLEN 34359738367ULL
#define LP_ENCODING_INT 0
#define LP_ENCODING_STRING 1

#define LP_ENCODING_7BIT_UINT 0
#define LP_ENCODING_7BIT_UINT_MASK 0x80
#define LP_ENCODING_IS_7BIT_UINT(byte)                                         \
  (((byte) & LP_ENCODING_7BIT_UINT_MASK) == LP_ENCODING_7BIT_UINT)

#define LP_ENCODING_6BIT_STR 0x80
#define LP_ENCODING_6BIT_STR_MASK 0xC0
#define LP_ENCODING_IS_6BIT_STR(byte)                                          \
  (((byte) & LP_ENCODING_6BIT_STR_MASK) == LP_ENCODING_6BIT_STR)

#define LP_ENCODING_13BIT_INT 0xC0
#define LP_ENCODING_13BIT_INT_MASK 0xE0
#define LP_ENCODING_IS_13BIT_INT(byte)                                         \
  (((byte) & LP_ENCODING_13BIT_INT_MASK) == LP_ENCODING_13BIT_INT)

#define LP_ENCODING_12BIT_STR 0xE0
#define LP_ENCODING_12BIT_STR_MASK 0xF0
#define LP_ENCODING_IS_12BIT_STR(byte)                                         \
  (((byte) & LP_ENCODING_12BIT_STR_MASK) == LP_ENCODING_12BIT_STR)

#define LP_ENCODING_16BIT_INT 0xF1
#define LP_ENCODING_16BIT_INT_MASK 0xFF
#define LP_ENCODING_IS_16BIT_INT(byte)                                         \
  (((byte) & LP_ENCODING_16BIT_INT_MASK) == LP_ENCODING_16BIT_INT)

#define LP_ENCODING_24BIT_INT 0xF2
#define LP_ENCODING_24BIT_INT_MASK 0xFF
#define LP_ENCODING_IS_24BIT_INT(byte)                                         \
  (((byte) & LP_ENCODING_24BIT_INT_MASK) == LP_ENCODING_24BIT_INT)

#define LP_ENCODING_32BIT_INT 0xF3
#define LP_ENCODING_32BIT_INT_MASK 0xFF
#define LP_ENCODING_IS_32BIT_INT(byte)                                         \
  (((byte) & LP_ENCODING_32BIT_INT_MASK) == LP_ENCODING_32BIT_INT)

#define LP_ENCODING_64BIT_INT 0xF4
#define LP_ENCODING_64BIT_INT_MASK 0xFF
#define LP_ENCODING_IS_64BIT_INT(byte)                                         \
  (((byte) & LP_ENCODING_64BIT_INT_MASK) == LP_ENCODING_64BIT_INT)

#define LP_ENCODING_32BIT_STR 0xF0
#define LP_ENCODING_32BIT_STR_MASK 0xFF
#define LP_ENCODING_IS_32BIT_STR(byte)                                         \
  (((byte) & LP_ENCODING_32BIT_STR_MASK) == LP_ENCODING_32BIT_STR)

#define LP_EOF 0xFF

#define LP_ENCODING_6BIT_STR_LEN(p) ((p)[0] & 0x3F)
#define LP_ENCODING_12BIT_STR_LEN(p) ((((p)[0] & 0xF) << 8) | (p)[1])
#define LP_ENCODING_32BIT_STR_LEN(p)                                           \
  (((uint32_t)(p)[1] << 0) | ((uint32_t)(p)[2] << 8) |                         \
   ((uint32_t)(p)[3] << 16) | ((uint32_t)(p)[4] << 24))

#define lpGetTotalBytes(p)                                                     \
  (((uint32_t)(p)[0] << 0) | ((uint32_t)(p)[1] << 8) |                         \
   ((uint32_t)(p)[2] << 16) | ((uint32_t)(p)[3] << 24))

#define lpGetNumElements(p) (((uint32_t)(p)[4] << 0) | ((uint32_t)(p)[5] << 8))

// 对字节进行操作，每次操作一个字节
#define lpSetTotalBytes(p, v)                                                  \
  do {                                                                         \
    (p)[0] = (v) & 0xff;                                                       \
    (p)[1] = ((v) >> 8) & 0xff;                                                \
    (p)[2] = ((v) >> 16) & 0xff;                                               \
    (p)[3] = ((v) >> 24) & 0xff;                                               \
  } while (0)

#define lpSetNumElements(p, v)                                                 \
  do {                                                                         \
    (p)[4] = (v) & 0xff;                                                       \
    (p)[5] = ((v) >> 8) & 0xff;                                                \
  } while (0)

/* Convert a string into a signed 64 bit integer.
 * The function returns 1 if the string could be parsed into a (non-overflowing)
 * signed 64 bit int, 0 otherwise. The 'value' will be set to the parsed value
 * when the function returns success.
 *
 * Note that this function demands that the string strictly represents
 * a int64 value: no spaces or other characters before or after the string
 * representing the number are accepted, nor zeroes at the start if not
 * for the string "0" representing the zero number.
 *
 * Because of its strictness, it is safe to use this function to check if
 * you can convert a string into a long long, and obtain back the string
 * from the number without any loss in the string representation. *
 *
 * -----------------------------------------------------------------------------
 *
 * Credits: this function was adapted from the Redis source code, file
 * "utils.c", function string2ll(), and is copyright:
 *
 * Copyright(C) 2011, Pieter Noordhuis
 * Copyright(C) 2011, Salvatore Sanfilippo
 *
 * The function is released under the BSD 3-clause license.
 */

/*
 * @describe: 将字符串转化为64位整数，成功返回1，失败返回0
 * @param: *s: 需要转换的字符串的指针
 *         *slen: 字符串长度
 *         *value: 转换后放置的位置
 */
int lpStringToInt64(const char *s, unsigned long slen, int64_t *value) {
  const char *p = s;
  unsigned long plen = 0;
  int negative = 0;
  uint64_t v;

  // 空字符串
  if (plen == slen)
    return 0;

  // 字符串长度为1，且第一个字符为0，value=0
  /* Special case: first and only digit is 0. */
  if (slen == 1 && p[0] == '0') {
    if (value != NULL)
      *value = 0;
    return 1;
  }

  // 字符串开头为'-'->是个负数
  if (p[0] == '-') {
    negative = 1;
    p++;
    plen++;

    // 只有一个-号转换失败
    /* Abort on only a negative sign. */
    if (plen == slen)
      return 0;
  }

  /* First digit should be 1-9, otherwise the string should just be 0. */
  if (p[0] >= '1' && p[0] <= '9') {
    v = p[0] - '0';
    p++;
    plen++;
    // case: "-0" -> 0
  } else if (p[0] == '0' && slen == 1) {
    *value = 0;
    return 1;
  } else {
    return 0;
  }

  while (plen < slen && p[0] >= '0' && p[0] <= '9') {
    // 处理溢出
    if (v > (UINT64_MAX / 10)) /* Overflow. */
      return 0;
    v *= 10;

    if (v > (UINT64_MAX - (p[0] - '0'))) /* Overflow. */
      return 0;
    v += p[0] - '0';

    p++;
    plen++;
  }

  /* Return if not all bytes were used. */
  if (plen < slen)
    return 0;

  // 转负数
  if (negative) {
    if (v > ((uint64_t)(-(INT64_MIN + 1)) + 1)) /* Overflow. */
      return 0;
    if (value != NULL)
      *value = -v;
  } else {
    if (v > INT64_MAX) /* Overflow. */
      return 0;
    if (value != NULL)
      *value = v;
  }
  return 1;
}

/* Create a new, empty listpack.
 * On success the new listpack is returned, otherwise an error is returned. */
unsigned char *lpNew(void) {
  /*
   * 分配空间
   * LP_HDR_SIZE: 6 头空间
   * 1: lpend  结束的尾部的空间
   * |     header   |   entries   |   end  |
   *   lpbytes+lplen      0          lplen
   */
  unsigned char *lp = lp_malloc(LP_HDR_SIZE + 1);
  if (lp == NULL)
    return NULL;
  // header: 6 end: 1
  lpSetTotalBytes(lp, LP_HDR_SIZE + 1);
  // 设置lp元素个数为0
  lpSetNumElements(lp, 0);
  lp[LP_HDR_SIZE] = LP_EOF;
  return lp;
}

/* Free the specified listpack. */
void lpFree(unsigned char *lp) { lp_free(lp); }
/*
 * 关于listpack的编码方式
 */

/* Given an element 'ele' of size 'size', determine if the element can be
 * represented inside the listpack encoded as integer, and returns
 * LP_ENCODING_INT if so. Otherwise returns LP_ENCODING_STR if no integer
 * encoding is possible.
 *
 * If the LP_ENCODING_INT is returned, the function stores the integer encoded
 * representation of the element in the 'intenc' buffer.
 *
 * Regardless of the returned encoding, 'enclen' is populated by reference to
 * the number of bytes that the string or integer encoded element will require
 * in order to be represented. */
/*
 * @describe: 返回编码方式
 * @param： *intenc->整数编码的保存位置
 *          *enclen->编码所需要的长度(无论什么形式)
 * @return:
 */
int lpEncodeGetType(unsigned char *ele, uint32_t size, unsigned char *intenc,
                    uint64_t *enclen) {
  int64_t v;
  if (lpStringToInt64((const char *)ele, size, &v)) {
    // small int: 0xxx xxxx
    if (v >= 0 && v <= 127) {
      /* Single byte 0-127 integer. */
      intenc[0] = v;
      *enclen = 1;
    } else if (v >= -4096 && v <= 4095) {
      /* 13 bit integer. */
      /* -4096 -> 1 0000 0000 0000   4095 -> 1111 1111 1111 */
      // 负数转为正数存储，第13位为1 -> 负数 0 -> 正数
      if (v < 0)
        v = ((int64_t)1 << 13) + v;

      /* 13位整数存储格式
       * 110|xxxxx yyyyyyyy */
      // 去掉低8为 与 0xc0(1100 0000) 前三位(110)为标志位
      intenc[0] = (v >> 8) | LP_ENCODING_13BIT_INT;
      // 低八位放在第2个字节
      intenc[1] = v & 0xff;
      *enclen = 2;
    } else if (v >= -32768 && v <= 32767) {
      /* 16 bit integer. */
      if (v < 0)
        v = ((int64_t)1 << 16) + v;
      intenc[0] = LP_ENCODING_16BIT_INT;
      intenc[1] = v & 0xff;
      intenc[2] = v >> 8;
      *enclen = 3;
    } else if (v >= -8388608 && v <= 8388607) {
      /* 24 bit integer. */
      if (v < 0)
        v = ((int64_t)1 << 24) + v;
      intenc[0] = LP_ENCODING_24BIT_INT;
      intenc[1] = v & 0xff;
      intenc[2] = (v >> 8) & 0xff;
      intenc[3] = v >> 16;
      *enclen = 4;
    } else if (v >= -2147483648 && v <= 2147483647) {
      /* 32 bit integer. */
      if (v < 0)
        v = ((int64_t)1 << 32) + v;
      intenc[0] = LP_ENCODING_32BIT_INT;
      intenc[1] = v & 0xff;
      intenc[2] = (v >> 8) & 0xff;
      intenc[3] = (v >> 16) & 0xff;
      intenc[4] = v >> 24;
      *enclen = 5;
    } else {
      /* 64 bit integer. */
      uint64_t uv = v;
      intenc[0] = LP_ENCODING_64BIT_INT;
      intenc[1] = uv & 0xff;
      intenc[2] = (uv >> 8) & 0xff;
      intenc[3] = (uv >> 16) & 0xff;
      intenc[4] = (uv >> 24) & 0xff;
      intenc[5] = (uv >> 32) & 0xff;
      intenc[6] = (uv >> 40) & 0xff;
      intenc[7] = (uv >> 48) & 0xff;
      intenc[8] = uv >> 56;
      *enclen = 9;
    }
    return LP_ENCODING_INT;
  }
  // 无法使用整数编码，返回字符编码类型 [len][str]
  else {
    if (size < 64)
      *enclen = 1 + size;
    else if (size < 4096)
      *enclen = 2 + size;
    else
      *enclen = 5 + size;
    return LP_ENCODING_STRING;
  }
}

/* Store a reverse-encoded variable length field, representing the length
 * of the previous element of size 'l', in the target buffer 'buf'.
 * The function returns the number of bytes used to encode it, from
 * 1 to 5. If 'buf' is NULL the funciton just returns the number of bytes
 * needed in order to encode the backlen. */
/*
 * @describe: 整数编码，存储在buf中，返回编码后的长度
 */
unsigned long lpEncodeBacklen(unsigned char *buf, uint64_t l) {
  if (l <= 127) {
    if (buf)
      buf[0] = l;
    return 1;
    // 2**14 = 16384
  } else if (l < 16383) {
    if (buf) {
      buf[0] = l >> 7;          // 第一个字节保存高7位
      buf[1] = (l & 127) | 128; // 第二个字节保存低7位 (字节的最高位为1)
    }
    return 2;
  } else if (l < 2097151) {
    if (buf) {
      buf[0] = l >> 14;
      buf[1] = ((l >> 7) & 127) | 128;
      buf[2] = (l & 127) | 128;
    }
    return 3;
  } else if (l < 268435455) {
    if (buf) {
      buf[0] = l >> 21;
      buf[1] = ((l >> 14) & 127) | 128;
      buf[2] = ((l >> 7) & 127) | 128;
      buf[3] = (l & 127) | 128;
    }
    return 4;
  } else {
    if (buf) {
      buf[0] = l >> 28;
      buf[1] = ((l >> 21) & 127) | 128;
      buf[2] = ((l >> 14) & 127) | 128;
      buf[3] = ((l >> 7) & 127) | 128;
      buf[4] = (l & 127) | 128;
    }
    return 5;
  }
}

/* Decode the backlen and returns it. If the encoding looks invalid (more than
 * 5 bytes are used), UINT64_MAX is returned to report the problem. */
/*
 * @describe: 解码数字编码，返回结果val
 * 这个解码长度需要给出被编码字段的最后一个字节，程序回溯会返回解码后的长度
 * 回溯的终点通过字节的首位0来确定
 */
uint64_t lpDecodeBacklen(unsigned char *p) {
  uint64_t val = 0;
  uint64_t shift = 0;
  // 每次循环取出一个字节的后7位
  do {
    val |= (uint64_t)(p[0] & 127) << shift;
    /*
     * 编码的过程中除了编码的第一个字节，其余的每个字节的最高位都为1
     * 0 xxx xxxx | 1 yyy yyyy | 1 zzz zzzz| ... | */
    if (!(p[0] & 128))
      break;
    shift += 7;
    p--;
    if (shift > 28)
      return UINT64_MAX;
  } while (1);
  return val;
}

/* Encode the string element pointed by 's' of size 'len' in the target
 * buffer 's'. The function should be called with 'buf' having always enough
 * space for encoding the string. This is done by calling lpEncodeGetType()
 * before calling this function. */
/*
 * @describe: 字符串编码
 *     tiny string
 *     multibytes string
 * entry: | encoding | data | len |
 * buf是要保存字符串编码的位置，从buf[0]开始记录encoding，
 * 将记录str和整个entry的长度的内存区域移动到encoding记录结束的位置
 *  <encoding> | tag | len |
 */
void lpEncodeString(unsigned char *buf, unsigned char *s, uint32_t len) {
  // tiny string: 10 | xxxxxx<string - data>
  if (len < 64) {
    buf[0] = len | LP_ENCODING_6BIT_STR; // 128 (1000 0000)
    memcpy(buf + 1, s, len);
  } else if (len < 4096) {
    buf[0] = (len >> 8) | LP_ENCODING_12BIT_STR;
    buf[1] = len & 0xff;
    memcpy(buf + 2, s, len);
  } else {
    buf[0] = LP_ENCODING_32BIT_STR;
    buf[1] = len & 0xff;
    buf[2] = (len >> 8) & 0xff;
    buf[3] = (len >> 16) & 0xff;
    buf[4] = (len >> 24) & 0xff;
    memcpy(buf + 5, s, len);
  }
}

/* Return the encoded length of the listpack element pointed by 'p'. If the
 * element encoding is wrong then 0 is returned. */
/*
 * @describe: 1. 若是整数编码：<entry> | encoding | len |
 *                 encoding部分包含了数据本身，<encoding> | tag | number |
 *
 *            2. 若是字符串编码：<entry> | enconding | data | len |
 *               <encoding>: | tag | len(str) |
 *               <data>: str
 *   调用这个函数会返回整个entry的长度，但这个长度不包含entry末尾的len
 */
uint32_t lpCurrentEncodedSize(unsigned char *p) {
  if (LP_ENCODING_IS_7BIT_UINT(p[0]))
    return 1;
  if (LP_ENCODING_IS_6BIT_STR(p[0]))
    return 1 + LP_ENCODING_6BIT_STR_LEN(p);
  if (LP_ENCODING_IS_13BIT_INT(p[0]))
    return 2;
  if (LP_ENCODING_IS_16BIT_INT(p[0]))
    return 3;
  if (LP_ENCODING_IS_24BIT_INT(p[0]))
    return 4;
  if (LP_ENCODING_IS_32BIT_INT(p[0]))
    return 5;
  if (LP_ENCODING_IS_64BIT_INT(p[0]))
    return 9;
  if (LP_ENCODING_IS_12BIT_STR(p[0]))
    return 2 + LP_ENCODING_12BIT_STR_LEN(p);
  if (LP_ENCODING_IS_32BIT_STR(p[0]))
    return 5 + LP_ENCODING_32BIT_STR_LEN(p);
  if (p[0] == LP_EOF)
    return 1;
  return 0;
}

/* Skip the current entry returning the next. It is invalid to call this
 * function if the current element is the EOF element at the end of the
 * listpack, however, while this function is used to implement lpNext(),
 * it does not return NULL when the EOF element is encountered. */
/* @describe: 从前往后，跳过当前的entry，返回后面的一个entry */
unsigned char *lpSkip(unsigned char *p) {
  unsigned long entrylen = lpCurrentEncodedSize(p);
  /* 对entrylen采用整数编码，返回的长度就是记录entry长度len所需要占用的空间*/
  entrylen += lpEncodeBacklen(NULL, entrylen);
  p += entrylen;
  return p;
}

/* If 'p' points to an element of the listpack, calling lpNext() will return
 * the pointer to the next element (the one on the right), or NULL if 'p'
 * already pointed to the last element of the listpack. */
/* 获取后一个元素，实际上就是函数lpSkip对到最后一个entry情况的处理*/
unsigned char *lpNext(unsigned char *lp, unsigned char *p) {
  ((void)lp); /* lp is not used for now. However lpPrev() uses it. */
  p = lpSkip(p);
  if (p[0] == LP_EOF)
    return NULL;
  return p;
}

/* If 'p' points to an element of the listpack, calling lpPrev() will return
 * the pointer to the preivous element (the one on the left), or NULL if 'p'
 * already pointed to the first element of the listpack. */
/* 返回前一个entry*/
unsigned char *lpPrev(unsigned char *lp, unsigned char *p) {
  // 已经是一个元素
  if (p - lp == LP_HDR_SIZE)
    return NULL;
  /*
   * | entry0 | entry1 | ... | entry(n-1) | entry(n) |
   *                                    |   |
   *                                   p--  p
   * 长度的采用的7位编码，lpDecodeBacklen会回溯到标志位为0的地方，返回长度prelen
   */
  p--; /* Seek the first backlen byte of the last element. */
  uint64_t prevlen = lpDecodeBacklen(p);
  prevlen += lpEncodeBacklen(NULL, prevlen);
  return p - prevlen + 1; /* Seek the first byte of the previous entry. */
}

/* Return a pointer to the first element of the listpack, or NULL if the
 * listpack has no elements. */
/* 返回第一个entry，指向listpack的指针+header的字节数
 */
unsigned char *lpFirst(unsigned char *lp) {
  lp += LP_HDR_SIZE; /* Skip the header. */
  if (lp[0] == LP_EOF)
    return NULL;
  return lp;
}

/* Return a pointer to the last element of the listpack, or NULL if the
 * listpack has no elements. */
// header的第一部分记录总字节数
unsigned char *lpLast(unsigned char *lp) {
  unsigned char *p = lp + lpGetTotalBytes(lp) - 1; /* Seek EOF element. */
  return lpPrev(lp, p); /* Will return NULL if EOF is the only element. */
}

/* Return the number of elements inside the listpack. This function attempts
 * to use the cached value when within range, otherwise a full scan is
 * needed. As a side effect of calling this function, the listpack header
 * could be modified, because if the count is found to be already within
 * the 'numele' header field range, the new value is set. */
uint32_t lpLength(unsigned char *lp) {
  uint32_t numele = lpGetNumElements(lp);
  if (numele != LP_HDR_NUMELE_UNKNOWN)
    return numele;

  /* Too many elements inside the listpack. We need to scan in order
   * to get the total number. */
  uint32_t count = 0;
  unsigned char *p = lpFirst(lp);
  while (p) {
    count++;
    p = lpNext(lp, p);
  }

  /* If the count is again within range of the header numele field,
   * set it. */
  if (count < LP_HDR_NUMELE_UNKNOWN)
    lpSetNumElements(lp, count);
  return count;
}

/* Return the listpack element pointed by 'p'.
 *
 * The function changes behavior depending on the passed 'intbuf' value.
 * Specifically, if 'intbuf' is NULL:
 *
 * If the element is internally encoded as an integer, the function returns
 * NULL and populates the integer value by reference in 'count'. Otherwise
 * if the element is encoded as a string a pointer to the string (pointing
 * inside the listpack itself) is returned, and 'count' is set to the length
 * of the string.
 *
 * If instead 'intbuf' points to a buffer passed by the caller, that must be
 * at least LP_INTBUF_SIZE bytes, the function always returns the element as
 * it was a string (returning the pointer to the string and setting the
 * 'count' argument to the string length by reference). However if the
 * element is encoded as an integer, the 'intbuf' buffer is used in order to
 * store the string representation.
 *
 * The user should use one or the other form depending on what the value
 * will be used for. If there is immediate usage for an integer value
 * returned by the function, than to pass a buffer (and convert it back to a
 * number) is of course useless.
 *
 * If the function is called against a badly encoded ziplist, so that there
 * is no valid way to parse it, the function returns like if there was an
 * integer encoded with value 12345678900000000 + <unrecognized byte>, this
 * may be an hint to understand that something is wrong. To crash in this
 * case is not sensible because of the different requirements of the
 * application using this lib.
 *
 * Similarly, there is no error returned since the listpack normally can be
 * assumed to be valid, so that would be a very high API cost. However a
 * function in order to check the integrity of the listpack at load time is
 * provided, check lpIsValid(). */
unsigned char *lpGet(unsigned char *p, int64_t *count, unsigned char *intbuf) {
  int64_t val;
  uint64_t uval, negstart, negmax;

  if (LP_ENCODING_IS_7BIT_UINT(p[0])) {
    negstart = UINT64_MAX; /* 7 bit ints are always positive. */
    negmax = 0;
    uval = p[0] & 0x7f;
  } else if (LP_ENCODING_IS_6BIT_STR(p[0])) {
    *count = LP_ENCODING_6BIT_STR_LEN(p);
    return p + 1;
  } else if (LP_ENCODING_IS_13BIT_INT(p[0])) {
    uval = ((p[0] & 0x1f) << 8) | p[1];
    negstart = (uint64_t)1 << 12;
    negmax = 8191;
  } else if (LP_ENCODING_IS_16BIT_INT(p[0])) {
    uval = (uint64_t)p[1] | (uint64_t)p[2] << 8;
    negstart = (uint64_t)1 << 15;
    negmax = UINT16_MAX;
  } else if (LP_ENCODING_IS_24BIT_INT(p[0])) {
    uval = (uint64_t)p[1] | (uint64_t)p[2] << 8 | (uint64_t)p[3] << 16;
    negstart = (uint64_t)1 << 23;
    negmax = UINT32_MAX >> 8;
  } else if (LP_ENCODING_IS_32BIT_INT(p[0])) {
    uval = (uint64_t)p[1] | (uint64_t)p[2] << 8 | (uint64_t)p[3] << 16 |
           (uint64_t)p[4] << 24;
    negstart = (uint64_t)1 << 31;
    negmax = UINT32_MAX;
  } else if (LP_ENCODING_IS_64BIT_INT(p[0])) {
    uval = (uint64_t)p[1] | (uint64_t)p[2] << 8 | (uint64_t)p[3] << 16 |
           (uint64_t)p[4] << 24 | (uint64_t)p[5] << 32 | (uint64_t)p[6] << 40 |
           (uint64_t)p[7] << 48 | (uint64_t)p[8] << 56;
    negstart = (uint64_t)1 << 63;
    negmax = UINT64_MAX;
  } else if (LP_ENCODING_IS_12BIT_STR(p[0])) {
    *count = LP_ENCODING_12BIT_STR_LEN(p);
    return p + 2;
  } else if (LP_ENCODING_IS_32BIT_STR(p[0])) {
    *count = LP_ENCODING_32BIT_STR_LEN(p);
    return p + 5;
  } else {
    uval = 12345678900000000ULL + p[0];
    negstart = UINT64_MAX;
    negmax = 0;
  }

  /* We reach this code path only for integer encodings.
   * Convert the unsigned value to the signed one using two's complement
   * rule. */
  if (uval >= negstart) {
    /* This three steps conversion should avoid undefined behaviors
     * in the unsigned -> signed conversion. */
    uval = negmax - uval;
    val = uval;
    val = -val - 1;
  } else {
    val = uval;
  }

  /* Return the string representation of the integer or the value itself
   * depending on intbuf being NULL or not. */
  if (intbuf) {
    *count = snprintf((char *)intbuf, LP_INTBUF_SIZE, "%lld", val);
    return intbuf;
  } else {
    *count = val;
    return NULL;
  }
}

/* Insert, delete or replace the specified element 'ele' of lenght 'len' at
 * the specified position 'p', with 'p' being a listpack element pointer
 * obtained with lpFirst(), lpLast(), lpIndex(), lpNext(), lpPrev() or
 * lpSeek().
 *
 * The element is inserted before, after, or replaces the element pointed
 * by 'p' depending on the 'where' argument, that can be LP_BEFORE, LP_AFTER
 * or LP_REPLACE.
 *
 * If 'ele' is set to NULL, the function removes the element pointed by 'p'
 * instead of inserting one.
 *
 * Returns NULL on out of memory or when the listpack total length would
 * exceed the max allowed size of 2^32-1, otherwise the new pointer to the
 * listpack holding the new element is returned (and the old pointer passed
 * is no longer considered valid)
 *
 * If 'newp' is not NULL, at the end of a successful call '*newp' will be
 * set to the address of the element just added, so that it will be possible
 * to continue an interation with lpNext() and lpPrev().
 *
 * For deletion operations ('ele' set to NULL) 'newp' is set to the next
 * element, on the right of the deleted one, or to NULL if the deleted
 * element was the last one. */
unsigned char *lpInsert(unsigned char *lp, unsigned char *ele, uint32_t size,
                        unsigned char *p, int where, unsigned char **newp) {
  unsigned char intenc[LP_MAX_INT_ENCODING_LEN];
  unsigned char backlen[LP_MAX_BACKLEN_SIZE];

  uint64_t enclen; /* The length of the encoded element. */

  /* An element pointer set to NULL means deletion, which is conceptually
   * replacing the element with a zero-length element. So whatever we
   * get passed as 'where', set it to LP_REPLACE. */
  /*
   * 三种操作方式: 1.insert before  2.insert after 3.replace (由where指定)
   * 操作位置: *p
   * 操作的元素: *ele(如果ele设置为null，相当于delete操作 将where的值赋值为1)
   */
  if (ele == NULL)
    where = LP_REPLACE;

  /* If we need to insert after the current element, we just jump to the
   * next element (that could be the EOF one) and handle the case of
   * inserting before. So the function will actually deal with just two
   * cases: LP_BEFORE and LP_REPLACE. */
  if (where == LP_AFTER) {
    p = lpSkip(p);
    where = LP_BEFORE;
  }

  /* Store the offset of the element 'p', so that we can obtain its
   * address again after a reallocation. */
  unsigned long poff = p - lp;

  /* Calling lpEncodeGetType() results into the encoded version of the
   * element to be stored into 'intenc' in case it is representable as
   * an integer: in that case, the function returns LP_ENCODING_INT.
   * Otherwise if LP_ENCODING_STR is returned, we'll have to call
   * lpEncodeString() to actually write the encoded string on place later.
   *
   * Whatever the returned encoding is, 'enclen' is populated with the
   * length of the encoded element. */
  int enctype;
  if (ele) {
    enctype = lpEncodeGetType(ele, size, intenc, &enclen);
  } else {
    enctype = -1;
    enclen = 0;
  }

  /* We need to also encode the backward-parsable length of the element
   * and append it to the end: this allows to traverse the listpack from
   * the end to the start. */
  // entry中的len的整数编码
  unsigned long backlen_size = ele ? lpEncodeBacklen(backlen, enclen) : 0;
  uint64_t old_listpack_bytes = lpGetTotalBytes(lp);
  uint32_t replaced_len = 0;
  // 如果采用replace的方式，需要额外减去被替换部分的字节数
  if (where == LP_REPLACE) {
    replaced_len = lpCurrentEncodedSize(p);
    replaced_len += lpEncodeBacklen(NULL, replaced_len);
  }
  // 计算新的listpack的字节数
  uint64_t new_listpack_bytes =
      old_listpack_bytes + enclen + backlen_size - replaced_len;
  if (new_listpack_bytes > UINT32_MAX)
    return NULL;

  /* We now need to reallocate in order to make space or shrink the
   * allocation (in case 'when' value is LP_REPLACE and the new element is
   * smaller). However we do that before memmoving the memory to
   * make room for the new element if the final allocation will get
   * larger, or we do it after if the final allocation will get smaller. */

  /* poff = p-lp
   * 记录插入位置的指针，其实就是传入参数p的值，后续指针p要参与计算*/
  unsigned char *dst = lp + poff; /* May be updated after reallocation. */

  /* Realloc before: we need more room. */
  /* 申请更多的内存*/
  if (new_listpack_bytes > old_listpack_bytes) {
    if ((lp = lp_realloc(lp, new_listpack_bytes)) == NULL)
      return NULL;
    /* 重新计算插入的位置，如果分配内存的时候内存块不够了，可能会重新申请内存块
     * 导致lp的地址发生了变化*/
    dst = lp + poff;
  }

  /* Setup the listpack relocating the elements to make the exact room
   * we need to store the new one. */
  /* 移动字节
   * <header> | <ele1> <ele2> | <end>
   *                   |
   *                  dst
   * 移动后:    <ele1>          <ele2>
   * 将从dst开始，往后到结束位置的字节(old_listpack_bytes-poff)
   * 移动到目的地址dst+elelen+backlen */
  if (where == LP_BEFORE) {
    memmove(dst + enclen + backlen_size, dst, old_listpack_bytes - poff);
  }
  /* 替换*/
  else { /* LP_REPLACE. */
    long lendiff = (enclen + backlen_size) - replaced_len;
    /*
     * 将从dis+replaced_len开始往后 old_listpack_bytes-poff-replaced_len
     * 个字节的空间 移动到
     * dis+replaced_len+lendiff的位置，
     * lendiff是替换的元素和先前测个位置元素的差值
     *                  replaced_len
     *            loff<--|<--->|-->old_listpack_bytes-poff-replaced_len
     * <header> | <ele1> <ele2> <ele3> | <end>
     *                   |      |
     *                  dst dis+replaced_len
     * 移动后:    <ele1>          <ele3>
     */
    memmove(dst + replaced_len + lendiff, dst + replaced_len,
            old_listpack_bytes - poff - replaced_len);
  }

  /* Realloc after: we need to free space. */
  // 比先前占用的空间少
  if (new_listpack_bytes < old_listpack_bytes) {
    if ((lp = lp_realloc(lp, new_listpack_bytes)) == NULL)
      return NULL;
    dst = lp + poff;
  }

  /* Store the entry. */
  // **newp 指针指针
  if (newp) {
    *newp = dst;
    /* In case of deletion, set 'newp' to NULL if the next element is
     * the EOF element. */
    if (!ele && dst[0] == LP_EOF)
      *newp = NULL;
  }
  if (ele) {
    if (enctype == LP_ENCODING_INT) {
      /* 整数的情况:
       * 整数是存储在intenc，整数的长度存储在enclen
       * 直接将这两块的内存移动到dst位置*/
      memcpy(dst, intenc, enclen);
    } else {
      /* 字符串的情况:
       * 字符串编码函数将结果放到dst位置*/
      lpEncodeString(dst, ele, size);
    }
    dst += enclen;
    /* <ele1> <ele2> <ele3>
     * <ele1> <  >   <ele3>
     * 释放减少的部分的空间
     * backlen： encoding+str 的长度的整数编码存储的位置
     * baclen_size: backlen的长度*/
    memcpy(dst, backlen, backlen_size);
    dst += backlen_size;
  }

  /* Update header. */
  /* 更新header中的num-elements */
  if (where != LP_REPLACE || ele == NULL) {
    uint32_t num_elements = lpGetNumElements(lp);
    if (num_elements != LP_HDR_NUMELE_UNKNOWN) {
      // 插入
      if (ele)
        lpSetNumElements(lp, num_elements + 1);
      // ele = NULL 删除
      else
        lpSetNumElements(lp, num_elements - 1);
    }
  }
  /* 更新header中的tot-bytes*/
  /* 注: tot_bytes占用4个字节，最多32位，所以整个listpack的size限制在了4gb */
  lpSetTotalBytes(lp, new_listpack_bytes);
  return lp;
}

/* Append the specified element 'ele' of lenght 'len' at the end of the
 * listpack. It is implemented in terms of lpInsert(), so the return value
 * is the same as lpInsert(). */
unsigned char *lpAppend(unsigned char *lp, unsigned char *ele, uint32_t size) {
  uint64_t listpack_bytes = lpGetTotalBytes(lp);
  /* 找到end位置，在前面插入*/
  unsigned char *eofptr = lp + listpack_bytes - 1;
  return lpInsert(lp, ele, size, eofptr, LP_BEFORE, NULL);
}

/* Remove the element pointed by 'p', and return the resulting listpack.
 * If 'newp' is not NULL, the next element pointer (to the right of the
 * deleted one) is returned by reference. If the deleted element was the
 * last one, '*newp' is set to NULL. */
unsigned char *lpDelete(unsigned char *lp, unsigned char *p,
                        unsigned char **newp) {
  return lpInsert(lp, NULL, 0, p, LP_REPLACE, newp);
}

/* Return the total number of bytes the listpack is composed of. */
uint32_t lpBytes(unsigned char *lp) { return lpGetTotalBytes(lp); }

/* Seek the specified element and returns the pointer to the seeked element.
 * Positive indexes specify the zero-based element to seek from the head to
 * the tail, negative indexes specify elements starting from the tail, where
 * -1 means the last element, -2 the penultimate and so forth. If the index
 * is out of range, NULL is returned. */
unsigned char *lpSeek(unsigned char *lp, long index) {
  int forward = 1; /* Seek forward by default. */

  /* We want to seek from left to right or the other way around
   * depending on the listpack length and the element position.
   * However if the listpack length cannot be obtained in constant time,
   * we always seek from left to right. */
  uint32_t numele = lpGetNumElements(lp);
  if (numele != LP_HDR_NUMELE_UNKNOWN) {
    if (index < 0)
      index = (long)numele + index;
    if (index < 0)
      return NULL; /* Index still < 0 means out of range. */
    if (index >= numele)
      return NULL; /* Out of range the other side. */
    /* We want to scan right-to-left if the element we are looking for
     * is past the half of the listpack. */
    /* 超过一半从后往前搜索*/
    if (index > numele / 2) {
      forward = 0;
      /* Left to right scanning always expects a negative index. Convert
       * our index to negative form. */
      index -= numele;
    }
  } else {
    /* If the listpack length is unspecified, for negative indexes we
     * want to always scan left-to-right. */
    if (index < 0)
      forward = 0;
  }

  /* Forward and backward scanning is trivially based on lpNext()/lpPrev().
   */
  if (forward) {
    unsigned char *ele = lpFirst(lp);
    while (index > 0 && ele) {
      ele = lpNext(lp, ele);
      index--;
    }
    return ele;
  } else {
    unsigned char *ele = lpLast(lp);
    while (index < -1 && ele) {
      ele = lpPrev(lp, ele);
      index++;
    }
    return ele;
  }
}
