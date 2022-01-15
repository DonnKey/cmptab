typedef unsigned long long bitstringMember;
struct bitstring {
    int maxIndex;       /* in bits */
    bitstringMember bits[1];       /* the bits; variable size */
};

typedef struct bitstring * bitstring; 

char *hexbits(bitstring str);
void x_set(bitstring *str, int bitindex);
void x_reset(bitstring *str, int bitindex);
boolean x_test(bitstring str, int bitindex);
void x_or(bitstring *str0, bitstring str1, bitstring str2);
void x_minus(bitstring *str0, bitstring str1, bitstring str2);
void x_setempty(bitstring *str);
void x_not(bitstring *str0, bitstring str1);
int x_count(bitstring str);
boolean x_empty(bitstring str);
boolean x_equal(bitstring str1, bitstring str2);
boolean x_empty_minus(bitstring str1, bitstring str2);
boolean x_empty_and(bitstring str1, bitstring str2);
long x_size(bitstring str);
bitstring newbits(bitstring str);
void freebits(bitstring *str);

#define NULLBITS ((bitstring)0)