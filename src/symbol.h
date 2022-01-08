/* #### Page 1 */
/* grammar and table common types */
typedef int vocab_symbol;
typedef bitstring set_of_syms;

/*
   V CONTAINS THE CHARACTER REPRESENTATION OF EACH SYMBOL IN THE VOCABULARY.
*/
#define MAX_NO_SYMS 255         /*  MAX NUMBER OF VOCABULARY SYMBOLS  */

extern char *v[MAX_NO_SYMS];

extern vocab_symbol no_terminals;       /*  NUMBER OF TERMINALS  */
extern vocab_symbol no_nts;     /*  NUMBER OF NON-TERMINALS  */
extern int largest_nt;  /*  THE ABOVE PLUS SOME SLOP  */
