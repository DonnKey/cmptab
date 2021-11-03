/* #### Page 1 */
struct bitstring {
            int length;         /* in bits */
            char bits[1];       /* the bits; variable size*/
        };

typedef struct bitstring * bitstring;

char *hexbits();
void x_set();
void x_reset();
boolean x_test();
void x_and();
void x_or();
void x_minus();
void x_setempty();
int x_count();
boolean x_empty();
boolean x_equal();
bitstring newbits();
void freebits();

#define NULLBITS ((bitstring)0)
