extern set_of_states goto_set[MAX_NO_SYMS];
extern set_of_states start_set[MAX_NO_PRODS];
extern set_of_rules in_start_set[MAX_NO_STATES];       /*  WITH STATE IN START SET  */
extern set_of_syms reduce_follow[MAX_NO_PRODS];        /*  FOLLOW SET FROM REDNS  */

void extract_grammar();
