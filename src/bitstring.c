/* #### Page 1 */
#include <memory.h>

#include "type.h"
#include "bitstring.h"
/*             ***************************************
               *                                     *
               *      bit str1ng manipulation        *
               *             routines                *
               *                                     *
               ***************************************
*/
/*
   all functions but x_not work as expected.  x_not assumes
   that the length specifies the universe, and thus a dummy
   set or reset must be used to guarantee that the last bit
   in the universe is in fact defined.
*/

char *hexbits(str)
/*  dump a bit str1ng in hex  */
bitstring str;
{
        int i;
        static char str2[200];
        int len;
   if (str == NULLBITS) return "NULLBITS";
   if (str->length == -1) {
        return "EMPTY";

   }
   len  = (str->length+8)/8;
   for (i=0 ; i < len && i < 200/2;  i++) {
        sprintf(&str2[2*i],"%2.2x",str->bits[i]&0xff);
   }
   return str2;
}
static bitstring x_bitstring(str)
bitstring str;
{
   int len;
   if (str == NULLBITS) {
      str =  (bitstring)malloc(sizeof(struct bitstring)+8/sizeof(char));
      str->length = -1;
      str->bits[0] = 0;
   }
   return str;
}

void x_set(str, bitindex)
/*  set a single bit  */
bitstring *str;
int bitindex;
{
   int i;
/* #### Page 2 */
   *str = x_bitstring(*str);
   if (bitindex < 0) return;
   if ((bitindex+8)/8 > ((*str)->length+8)/8)  {
     *str  = (bitstring) realloc(*str,sizeof(struct bitstring) + (bitindex+8)/8);
     for  (i=((*str)->length+8)/8+i;i <= (bitindex+8)/8; i++) (*str)->bits[i]=0;
   }
   if ((*str)->length < bitindex) (*str)->length = bitindex;
   (*str)->bits[bitindex/8]  |= 0x80>>bitindex%8;
}
void x_reset(str, bitindex)
/*  clear a single bit  */
bitstring *str;
int bitindex;
{
   int i;

   *str = x_bitstring(*str);
   if (bitindex < 0) return;
   if ((bitindex+8)/8 > ((*str)->length+8)/8) {
     *str  = (bitstring) realloc(*str,sizeof(struct bitstring) + (bitindex+8)/8);
      for (i=((*str)->length+8)/8+i;i <= (bitindex+8)/8;  i++)(*str)->bits[i]=0;
   }
   if ((*str)->length < bitindex) (*str)->length = bitindex;
   (*str)->bits[bitindex/8] &= ~(0x80>>bitindex%8);
}

boolean x_test(str, bitindex)
/*  return value of a single bit  */
bitstring str;
int bitindex;
{
   if (bitindex > str->length) return 0;
   if (bitindex < 0) return 0;
   return (str->bits[bitindex/8] & (0x80>>(bitindex%8))) != 0;
}

void x_and(str0, str1, str2)
/* the logical product of two bit str1ngs  */
bitstring *str0, str1, str2;
{
   bitstring  str3;
   int i,len;

   *str0 = x_bitstring(*str0);
   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);
   if (str2->length > str1->length) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }
   /*  strl is now the longer; the result will be  truncated to the length
       of str2 */
   len = (str2->length+8)/8;
/* #### Page 3 */
   if (((*str0)->length+8)/8  < len) {
       *str0  = (bitstring) realloc(*str0, sizeof(struct bitstring)+len);
     for (i=((*str0)->length+8)/8+1;i  <= len; i++) (*str0)->bits[i]=0;
   }
   len--;
   for (i =0;  i<len; i++) {
      (*str0)->bits[i] = str2->bits[i] & str1->bits[i];
   }
   (*str0)->bits[len] = str2->bits[len] & str1->bits[len] &
               ~(0x7f  >> (str2->length%8));
   (*str0)->length = str2->length;
}

void x_or(str0, str1, str2)
/* the logical sum of two bit str1ngs  */
bitstring *str0, str1, str2;
{
   bitstring  str3;
   int i,len;

   *str0 = x_bitstring(*str0);
   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);
   if (str2->length > str1->length) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }
   /*  str1 is now the longer; the result will be  that of str1 */
   len = (str1->length+8)/8;
   if (((*str0)->length+8)/8 < len) {
        *str0 = (bitstring) realloc(*str0, sizeof(struct bitstring)+len);
      for (i=((*str0)->length+8)/8+1;i <= len;  i++)(*str0)->bits[i]=0;
   }
   len = (str2->length+8)/8;
   len--;
   for (i = 0; i<len; i++) {
      (*str0)->bits[i] = str2->bits[i]  |str1->bits[i];
   }
   (*str0)->bits[len] = str1->bits[len]  |
           (str2->bits[len] & ~(0x7f >>  (str2->length%8)));
   (*str0)->length = str1->length;
}

void x_not(str0,str1)
bitstring *str0, str1;
/*  inverse of a bit str1ng up to the last  defined bit  */
{
   int i,len;

   *str0 = x_bitstring(*str0);
   str1 = x_bitstring(str1);
   len = (str1->length+8)/8;
   if ((*str0)->length < str1->length) {
        *str0 = (bitstring)realloc(*str0,  sizeof(struct bitstring)+len);
/* #### Page 4 */
      for (i=((*str0)->length+8)/8+1;i <= len; i++)  (*str0)->bits[i]=0;
   }
   len--;
   for (i=0; i<len; i++) {
      (*str0)->bits[i] = ~str1->bits[i];
   }
   (*str0)->bits[len] = ~str1->bits[len] & ~(0x7f>>(str1->length%8) );

}
boolean x_equal(str1, str2)
bitstring str1, str2;
{
   bitstring  str3;
   int i,len1,len2,bits2;

   if (str1->length == -1 && str2->length == -1)  return 1;
   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);
   if (str2->length > str1->length) {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }

  /*   str1 is now the longer */

   len1  = (str1->length+8)/8 - 1;
   if (str2->length != -1) {
      len2 = (str2->length+8)/8 - 1;

      /* compare common prefix*/
      for (i = 0; i<len2; i++) {
         if (str2->bits[i] != str1->bits[i])  return 0;
      }

      /* compare trailing partial byte */
      if ((str1->bits[len2] & ~(0x7f >>  (str2->length%8))) !=
          (str2->bits[len2] & ~(0x7f >>  (str2->length%8)))) return 0;
      bits2 = str2->length%8+1;
   }
   else {
      len2 = 0;
      bits2 = 0;
   }
   if (str1->length == str2->length) return  1;

   /*  if lengths differ all trailing bits must  be zero */
   if (len1 > len2) {
           /* all of one chunk, plus maybe more,  and a trailing part */
           if ((str1->bits[len2] &  (0xff >> bits2)) != 0) return 0;

           /* then whole bytes */
           for (i = len2+1; i<len1; i++)  {
              if (str1->bits[i] !=0 )  return 0;
/* #### Page 5 */
          }
           /* and the partial chunk */
           if ((str1->bits[len1] & ~(0x7f  >> (str1->length%8))) != 0) return 0;
   }
   else {
        /* a few more bits in one chunk  */
           if ((str1->bits[len2] & (0xff  >> bits2)
                                 & ~(0x7f  >> (str1->length%8))) != 0) return 0;
   }
   return 1;
}

void x_minus(str0, str1, str2)
bitstring *str0,str1, str2;
{
   bitstring str3;
   int i,len;

   *str0 = x_bitstring(*str0);
   str1 = x_bitstring(str1);
   str2 = x_bitstring(str2);
   if (str2->length > str1->length)  {
      str3 = str1;
      str1 = str2;
      str2 = str3;
   }
   /*  str1 is now the longer; the  result will be truncated to the length
       of str2 */
   len = (str2->length+8)/8;
   if (((*str0)->length+8)/8 < len)  {
        *str0 = (bitstring) realloc(*str0,  sizeof(struct bitstring)+len);
      for (i=((*str0)->length+8)/8+1;i  <= len; i++) (*str0)->bits[i]=0;
   }
   len--;
   for (i = 0; i<len; i++) {
      (*str0)->bits[i] = str2->bits[i] &  ~str1->bits[i];
   }
   (*str0)->bits[len] = str2->bits[len]  &
                ~(str1->bits[len] &  ~(0x7f >> (str2->length%8)));
   (*str0)->length = str2->length;
}
int x_count(str)
/*  count number of elements  (ones)  */
bitstring str;
{
   int i, j, count;
   char item;
   int len;

   str = x_bitstring(str);
   len = str->length;
   if (len == -1) return 0;
   len = (len+8)/8 - 1;
   count = 0;
   for (i=0; i<len; i++)  {
/* #### Page 6 */
      item  = str->bits[i];
      if (item != 0) {
         for (j=0; j<8; j++) {
            if (((item >> j) & 1) != 0) count = count + 1;
         }
      }
   }
   item = str->bits[len] & ~(0x7f>>(str->length%8));
   if (item != 0) {
      for (j=0; j<8; j++) {
         if (((item >> j) & 1) != 0) count = count + 1;
      }
   }
   return count;
}

boolean x_empty(str)
/*  test for empty set  */
bitstring str;
{
   int i,len;

   if (str == NULLBITS) return 1;
   if (str->length == -1) return 1;
   str = x_bitstring(str);
   len = (str->length+8)/8;

   len--;
   for (i=0 ; i<len; i++) {
      if (str->bits[i] != 0) return 0;
   }
   i = str->bits[len] & ~(0x7f >> (str->length%8));
   return (i == 0);
}

bitstring newbits(str)
bitstring str;
{
        bitstring s;

        s = (bitstring) malloc(sizeof(struct  bitstring)+(str->length+8)/8);
        memcpy(s,str,sizeof(struct bitstring)+(str->length+8)/8 );
        return s;
}
void freebits(s)
 bitstring*s;
{
        if (*s != NULLBITS) free(*s);
        *s = NULLBITS;
}

void x_setempty(str)
bitstring *str;
{
/* #### Page 7 */
        freebits(str);
        *str=x_bitstring(*str);
}
