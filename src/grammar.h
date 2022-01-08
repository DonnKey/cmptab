/* #### Page 1 */
#define MAX_NO_PRODS 255        /*  MAX NUMBER OF PRODUCTIONS  */

#define MAX_NO_PROD_SYMBOLS 2047        /*  TOTAL ALL SYMBOLS, ALL PRODUCTIONS  */

typedef short production_symbols_ptr;
typedef char production_ptr;

/*
     PROD_ARRAY CONTAINS THE ELEMENTS OF ALL PRODUCTIONS AS VOCAB_SYMBOLS,
     WHICH ARE INDICES INTO V, THE VOCABULARY. PROD_ARRAY_PTR POINTS TO
     THE LAST ENTRY USED IN PROD_ARRAY.
     PROD_START CONTAINS ONE ENTRY FOR EACH PRODUCTION, AND POINTS TO THE
     L.H.S. OF THE PRODUCTION.  PARALLEL ARRAY RHS_LEN CONTAINS THE
     NUMBER OF SYMBOLS IN THE R.H.S.  ALL PRODUCTIONS CONTAIN THEIR L.H.S.
     (NO ABBREVIATION).
*/
extern vocab_symbol prod_array[MAX_NO_PROD_SYMBOLS];
extern production_symbols_ptr prod_array_ptr;
extern production_symbols_ptr prod_start[MAX_NO_PRODS];
extern counter rhs_len[MAX_NO_PRODS];

extern production_ptr no_prods;         /*  NUMBER OF PRODUCTIONS  */
extern vocab_symbol goal_symbol;        /*  ELEMENT OF V CHOSEN FOR GOAL  */

#define unspec_len 255  /*  LENGTH OF RULE UNSPECIFIED  */

#define first_nt (no_terminals + 1)
#define last_nt (no_terminals + no_nts)
