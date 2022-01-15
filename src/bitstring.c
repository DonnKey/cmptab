#include <memory.h>
#include <assert.h>

#include "type.h"
#include "bitstring.h"
/*             **************************************
               *                                    *
               *      bit string manipulation       *
               *             routines               *
               *                                    *
               **************************************
*/
/*
   all functions but x_not work as expected.  x_not assumes
   that the length specifies the universe, and thus a dummy
   set or reset must be used to guarantee that the last bit
   in the universe is in fact defined.
*/

/*
NOTE: the C implementation hews very closely to the XPL/S, and consequently
probably leaks (XPL garbage collected strings).  Not worth the effort for
an inherently short-lived program such as this, although if rewriting in a
modern language, it would be easy enough to fix.
*/

#define bitsPerByte 8
#define bsWord(pos) ((pos)/(sizeof(bitstringMember)*bitsPerByte))
#define bsBit(pos) ((pos)%(sizeof(bitstringMember)*bitsPerByte))
#define bsLen(str) (bsWord((str)->maxIndex)+1)
#define bsTopBit 0x8000000000000000ULL
#define bsAllBits 0xffffffffffffffffULL
#define bsOtherBits 0x7fffffffffffffffULL

char *hexbits(bitstring str)
/*  dump a bit string in hex  */
{
   int i;
   int len;

   if (str == NULLBITS) {
      return "NULLBITS";
   }
   if (str->maxIndex == -1) {
        return "EMPTY";
   }
   if (str->maxIndex < -1) {
        return "ILLFORMED";
   }

   char *str2 = (char*)malloc(220); /* this leaks */
   len = bsLen(str);
   int p = 0;
   for (i=0 ; i < len && i < 200/sizeof(bitstringMember); i++) {
       p += sprintf(&str2[8*i],"%16.16llx",str->bits[i]);
   }
   sprintf(&str2[p], " (%d)", str->maxIndex);
   return str2;
}

static bitstring x_bitstring(bitstring str)
{
   if (str == NULLBITS) {
      str = (bitstring)malloc(sizeof(struct bitstring));
      str->maxIndex = -1;
      str->bits[0] = 0;
   }
   return str;
}

void x_set(bitstring *str, int bitindex)
{
   /*  set a single bit   */
   int i;
   *str = x_bitstring(*str);
   if (bitindex < 0) {
      return;
   }
   if (bsWord(bitindex)+1 > bsLen(*str)) {
      *str = (bitstring) realloc(*str,sizeof(struct bitstring) + (bsWord(bitindex)+1)*sizeof(bitstringMember));
      for (i=bsLen(*str); i <= bsWord(bitindex); i++) (*str)->bits[i]=0;
   }
   if ((*str)->maxIndex < bitindex) (*str)->maxIndex = bitindex;
   (*str)->bits[bsWord(bitindex)] |= bsTopBit>>bsBit(bitindex);
   assert((*str)->maxIndex >= 0);
}

void x_reset(bitstring *str, int bitindex)
{
   /*  clear a single bit  */
   int i;

   *str = x_bitstring(*str);
   if (bitindex < 0) {
      return;
   }
   if (bsWord(bitindex)+1 > bsLen(*str)) {
      *str = (bitstring) realloc(*str,sizeof(struct bitstring) + (bsWord(bitindex)+1)*sizeof(bitstringMember));
      for (i=bsLen(*str); i <= bsWord(bitindex); i++) (*str)->bits[i]=0;
   }
   if ((*str)->maxIndex < bitindex) (*str)->maxIndex = bitindex;
   (*str)->bits[bsWord(bitindex)] &= ~(bsTopBit>>bsBit(bitindex));
   assert((*str)->maxIndex >= 0);
}

boolean x_test(bitstring str, int bitindex)
{
   /*  return value of a single bit  */
   if (str == NULLBITS) {
      return false;
   }
   if (bitindex < 0) {
      return false;
   }
   if (bitindex > str->maxIndex) {
      return false;
   }
   return (str->bits[bsWord(bitindex)] & (bsTopBit>>(bsBit(bitindex)))) != 0;
}

void x_and(bitstring *str0, bitstring str1, bitstring str2)
{
   /* the logical product of two bit strings */
   bitstring str3;
   bitstring res;
   int i,len;

   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);

   if (str1->maxIndex < 0 || str2->maxIndex < 0) {
      *str0 = NULLBITS;
      return;
   }
   if (str2->maxIndex > str1->maxIndex) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }
   /*  str1 is now the longer; the result will be truncated to the length
       of str2 */
   len = bsLen(str2);
   res = (bitstring) malloc(sizeof(struct bitstring)+len*sizeof(bitstringMember));
   res->maxIndex = str2->maxIndex;

   for (i = 0; i<len; i++) {
      res->bits[i] = str2->bits[i] & str1->bits[i];
   }
   res->bits[len-1] &= ~(bsOtherBits >> bsBit(res->maxIndex));
   assert(res->maxIndex >= 0);
   *str0 = res;
}

void x_or(bitstring *str0, bitstring str1, bitstring str2)
{
   /* the logical sum of two bit strings; will be the length of the longer  */
   bitstring str3;
   int i,len;
   bitstring res;

   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);

   if (str1->maxIndex < 0) {
      *str0 = newbits(str2);
      return;
   }
   if (str2->maxIndex < 0) {
      *str0 = newbits(str1);
      return;
   }
   if (str2->maxIndex > str1->maxIndex) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }
   /* str1 is now the longer; the result will be that of str1 */
   len = bsLen(str1);
   res = (bitstring) malloc(sizeof(struct bitstring)+len*sizeof(bitstringMember));
   res->maxIndex = str1->maxIndex;

   /* combine the common prefix */
   len = bsLen(str2);
   for (i = 0; i<len; i++) {
      res->bits[i] = str1->bits[i] | str2->bits[i];
   }

   /* just copy the remainder; clip the last byte */
   len = bsLen(str1);
   for (; i<len; i++) {
      res->bits[i] = str1->bits[i];
   }
   res->bits[len-1] &= ~(bsOtherBits >> bsBit(res->maxIndex));
   assert(res->maxIndex >= 0);
   *str0 = res;
}

void x_not(bitstring *str0, bitstring str1)
{
   /*  inverse of a bit string up to the last defined bit  */
   int i,len;
   bitstring res;

   len = bsLen(str1);
   res = (bitstring)malloc(sizeof(struct bitstring)+len*sizeof(bitstringMember));
   res->maxIndex = str1->maxIndex;

   for (i=0; i<len; i++) {
      res->bits[i] = ~str1->bits[i];
   }
   res->bits[len-1] &= ~(bsOtherBits >> bsBit(res->maxIndex));
   assert(res->maxIndex >= 0);
   *str0 = res;
}

boolean x_equal(bitstring str1, bitstring str2)
{
   bitstring str3;
   int i,len1,len2,bits2;

   if (str1->maxIndex == -1 && str2->maxIndex == -1) {
      return true;
   }
   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);
   if (str2->maxIndex > str1->maxIndex) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }

   /*  str1 is now the longer */
   len1 = bsLen(str1)-1;
   if (str2->maxIndex != -1) {
      len2 = bsLen(str2)-1;

      /* compare common prefix*/
      for (i = 0; i<len2-1; i++) {
         if (str2->bits[i] != str1->bits[i]) {
            return false;
         }
      }

      /* compare trailing partial word */
      if ((str1->bits[len2] & ~(bsOtherBits >> bsBit(str2->maxIndex))) !=
          (str2->bits[len2] & ~(bsOtherBits >> bsBit(str2->maxIndex)))) {
         return false;
      }
      bits2 = bsBit(str2->maxIndex);
   }
   else {
      len2 = 0;
      bits2 = 0;
   }

   if (str1->maxIndex == str2->maxIndex) {
      return true;
   }

   /* if lengths differ all trailing bits must be zero */
   if (len1 > len2) {
      /* remainder of one word, plus maybe more, and a trailing part. */
      if ((str1->bits[len2] & (bsAllBits >> bits2)) != 0) {
         return false;
      }

      /* then remaining whole chunks */
      for (i = len2+1; i<len1-1; i++) {
         if (str1->bits[i] != 0) {
            return false;
         }
      }
      /* and the partial chunk */
      if ((str1->bits[len1] & ~(bsOtherBits >> bsBit(str1->maxIndex))) != 0) {
         return false;
      }
   }
   else {
      /* a few more bits in one chunk */
      if ((str1->bits[len2] & (bsAllBits >> bits2)
                            & ~(bsOtherBits >> bsBit(str1->maxIndex))) != 0) {
         return false;
      }
   }
   return true;
}

void x_minus(bitstring *str0, bitstring str1, bitstring str2)
{
   bitstring str3;
   str1 = x_bitstring(str1);

   str3 = newbits(str2);
   if (str3->maxIndex < str1->maxIndex) {
      x_reset(&str3, str1->maxIndex);
   }
   x_not(&str3, str3);
   x_and(str0, str1, str3);

   freebits(&str3);
}

int x_count(bitstring str)
{
   /*  count number of elements (ones)  */
   int i, j, count;
   bitstringMember item;
   int len;

   str = x_bitstring(str);
   if (str->maxIndex == -1) {
      return 0;
   }

   len = bsLen(str);
   count = 0;
   for (i=0; i<len-1; i++) {
      item = str->bits[i];
      if (item != 0) {
         for (j=0; j < bitsPerByte*sizeof(bitstringMember); j++) {
            if (((item >> j) & 1) != 0) count = count + 1;
         }
      }
   }

   item = str->bits[len-1] & ~(bsOtherBits>>bsBit(str->maxIndex));
   if (item != 0) {
      for (j=0; j < bitsPerByte*sizeof(bitstringMember); j++) {
         if (((item >> j) & 1) != 0) count = count + 1;
      }
   }
   return count;
}

boolean x_empty(bitstring str)
{
   /*  test for empty set  */
   int len;
   bitstringMember i;

   if (str == NULLBITS) {
      return true;
   }
   if (str->maxIndex == -1) {
      return true;
   }
   str = x_bitstring(str);
   len = bsLen(str);

   for (i=0 ; i<len-1; i++) {
      if (str->bits[i] != 0) {
         return false;
      }
   }
   i = str->bits[len-1] & ~(bsOtherBits>>bsBit(str->maxIndex));
   return (i == 0);
}

bitstring newbits(bitstring str)
{
   bitstring s;
   int len;

   str = x_bitstring(str);
   len = sizeof(struct bitstring) + bsLen(str)*sizeof(bitstringMember);

   s = (bitstring) malloc(len);
   if (str == NULLBITS) {
      memset(s, 0, len);
      s->maxIndex = -1;
   }
   else {
      memcpy(s,str,len);
   }
   return s;
}

void freebits(bitstring *s)
{
   if (*s != NULLBITS) free(*s);
   *s = NULLBITS;
}

void x_setempty(bitstring *str)
{
   freebits(str);
   *str=newbits(NULLBITS);
}

long x_size(bitstring str) 
{
   return sizeof(struct bitstring)+bsLen(str);
}

boolean x_empty_minus(bitstring str1, bitstring str2)
{
   bitstring str;
   boolean foo;

   str=NULLBITS;
   x_minus(&str, str1, str2);
   foo = x_empty(str);
   freebits(&str);
   return foo;
}

boolean x_empty_and(bitstring str1, bitstring str2)
{
   bitstring str;
   boolean foo;

   str=NULLBITS;
   x_and(&str, str1, str2);
   foo = x_empty(str);
   freebits(&str);
   return foo;
}
