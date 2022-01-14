/* #### Page 1 */
/* PORTIONS OF THIS PROGRAM HAVE BEEN BORROWED FROM THE SLR1 PARSER GENERATPR
   BY F. DEREMER, originally written in XPL */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "type.h"
#include "utility.h"
#include "bitstring.h"
#include "nextitem.h"
#include "options.h"

#include "symbol.h"
#include "grammar.h"
#include "table.h"

#include "tableio.h"
#include "tabbinio.h"
#include "extractg.h"

FILE *mso;

#define MAX_NO_SPLITS 10        /*  NUMBER OF REDUCES SIMUTANEOUSLY SPLITTING A NT  */

boolean list_trace;
/*
                        ********************************
                        *                              *
                        x           GRAMMARS           *
                        *                              *
                        ********************************
*/

char *v[MAX_NO_SYMS] = {""};

vocab_symbol no_terminals;      /*  NUMBER OF TERMINALS  */
vocab_symbol no_nts;            /*  NUMBER OF NON-TERMINALS  */
int largest_nt;                 /*  THE ABOVE PLUS SOME SLOP */

vocab_symbol prod_array[MAX_NO_PROD_SYMBOLS];
production_symbols_ptr prod_array_ptr = 1;
production_symbols_ptr prod_start[MAX_NO_PRODS];
counter rhs_len[MAX_NO_PRODS];

production_ptr no_prods;        /*  NUMBER OF PRODUCTIONS  */
vocab_symbol goal_symbol;       /*  ELEMENT OF V CHOSEN FOR GOAL  */

char *deleted_nont = "0101";                    /*  NEVER IN INPUT!  */

set_of_syms lhs_used = NULLBITS;                /*  NT'S ON THE LEFT  */
set_of_syms nt_uncombinable[MAX_NO_SYMS];       /*  NT'S CAN'T BE COMBINED  */
set_of_states goto_set[MAX_NO_SYMS];

set_of_states start_set[MAX_NO_PRODS];
set_of_syms reduce_follow[MAX_NO_PRODS];        /*  FOLLOW SET FROM REDNS  */
set_of_rules lr_k_essential = NULLBITS;
/* #### Page 2 */
set_of_rules preferred_rules = NULLBITS;        /*  BE NICE TO ELIM NEXT  */

set_of_rules in_start_set[MAX_NO_STATES];       /*  WITH STATE IN START SET  */
bitstring marks[MAX_NO_STATES];                 /*  USED IN PHI-INACCESIBLITY  */

/*                   *********************************
                     *                               *
                     *       FIND INACCESSIBLES      *
                     *                               *
                     *********************************
*/

void find_all_inaccessibles()
{
  /*   THIS PROCEDURE COMPUTES THE FULL LR PHI-INACCESSIBILITY FOR THE TABLE  */
   set_of_syms f = NULLBITS;
   set_of_states p = NULLBITS, p_plus_1 = NULLBITS;
   vocab_symbol sym, t_sym;
   table_state state_no, s, goto_state;
   action action_t;
   int i;       /*  POSITION IN A RHS) */
   rule_no prod;
   boolean changed;
   table_entry actn_entry;
   set_of_syms lhs_ok = NULLBITS;
   vocab_symbol lhs;
   x_setempty(&lhs_ok);
   x_setempty(&lhs_used);
   x_setempty(&p);
   x_setempty(&p_plus_1);

   do {

      changed = false;

      for (state_no = 0; state_no <= no_states; state_no++) {
         if (!x_test(lhs_ok, accessing_symbol[state_no]))
             x_setempty(&marks[state_no]);
      }

      for (prod = 1; prod <= no_prods; prod++) {
         lhs = prod_array[prod_start[prod]];

         for (state_no = 0; state_no <= no_states; state_no++) {
            /*  IF THE STATE CONTAINS A RX ENTRY THEN COMPUTE P  */

            if (x_test(reduce_set[prod], state_no)) {
               actn_entry = action_pair(false, REDUCE, prod);

               x_setempty(&f);
               for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
                  if (stripped_action_table(state_no, t_sym) == actn_entry)
                      x_set(&f, t_sym);
               }
/* #### Page 3 */
               if (!x_empty(f)) {
                  x_setempty(&p);
                  x_set(&p, state_no);
                  i = rhs_len[prod];
                  while (i > 0) {
                     x_setempty(&p_plus_1);
                     sym = prod_array[prod_start[prod] + i];
                     for (s = 0; s <= no_states; s++) {
                        actn_entry = stripped_action_table(s, sym);
                        if (action_type(actn_entry) == SHIFT &&
                            x_test(p, action_state(actn_entry)))
                              x_set(&p_plus_1, s);
                     }
                     freebits(&p);
                     p = p_plus_1;
                     p_plus_1 = NULLBITS;
                     i = i - 1;
                  }

                  /*  WE HAVE THE PSEUDO START SET  */
                  for (s = 0; s <= no_states; s++) {
                     if (x_test(p, s)) {
                        x_set(&marks[s], lhs);
                        x_set(&lhs_used, lhs);
                        if (!x_test(lhs_ok, lhs)) {
                           /*  IT WOULD BE NICE TO BE ABLE TO DO THIS TEST
                           SOONER BUT WE MUST HAVE P TO MARK ALL COLUMNS EVEN
                           THOUGH WE NEED TO MARK ONLY SELECTED ROWS IN A
                           SECOND PASS  */
                           goto_state = action_state(stripped_action_table(s, lhs));
                           actn_entry = action_pair(false, REDUCE, prod);
                           for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
                              if (stripped_action_table(goto_state, t_sym) !=actn_entry
                                 && x_test(f, t_sym))
                                    x_set(&marks[goto_state], t_sym);
                           }
                        }
                     }
                  }
               }
            }
         }
      }
      for (sym= 0; sym <= last_nt; sym++) {
        x_set(&lhs_ok, sym);
      }

      /*  APPLY THE MARKS  */
      for (state_no = 0; state_no <= no_states; state_no++) {
         if (accessing_symbol[state_no] >= first_nt) {
           for (sym = 1; sym <= last_nt; sym++) {
               action_t = action_type(stripped_action_table(state_no, sym));
               if (x_test(marks[state_no], sym)) {
                  if (action_t == PHI || action_t == ESSENTIAL_ERROR) {
                     action_table(state_no, sym) = error_entry;
                  }
/* #### Page 4 */
               }
               else if (action_t != PHI) {
                  if (control[sd]) {
                     printf("Inaccessible entry %s at state %d and column %d was removed.\n",
                     format_action(stripped_action_table(state_no, sym)), state_no, sym);
                  }
                  if (action_t == REDUCE) {
                     prod = action_rule(stripped_action_table(state_no, sym));
                     x_reset(&reduce_follow[prod], sym);
                     changed = true;
                     /*  WE HAVE ZAPPED A REDUCE ENTRY, TRY AGAIN  */
                     x_reset(&lhs_ok, prod_array[prod_start[prod]]);
                  }
                  action_table(state_no, sym) = phi_entry;
               }
            }
         }
         else if (accessing_symbol[state_no] != 0) {
            for(sym = 1; sym <= no_terminals; sym++) {
               if (action_type(stripped_action_table(state_no, sym)) == PHI) {
                  action_table(state_no, sym) = error_entry;
               }
            }
         }
      }
   } while (changed);
   freebits(&p);
   freebits(&f);
   freebits(&lhs_ok);
}
void check_lhs_use()
{
   /*  CHECKS TO SEE IF THE LHS IS USED  */
   table_state state_no;
   vocab_symbol sym, t_sym;
   boolean state_removed;
   table_entry actn;

   state_removed = false;
   for (sym = first_nt; sym <= last_nt; sym++) {
     if (!x_test(lhs_used, sym)) {
         if (list_trace) {
           printf("Symbol %s is never on the left and thus removed.\n",v[sym]);
         }
         for (state_no = 0; state_no <= no_states; state_no++) {
            action_table(state_no, sym) = phi_entry;
            if (accessing_symbol[state_no] == sym) {
               if (list_trace) printf("State %d was removed.\n",state_no);
               state_removed = true;
               accessing_symbol[state_no] = 0;
               for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
                  action_table(state_no, t_sym) = phi_entry;
               }
            }
         }
      }
   }
/* #### Page 5 */

   while (state_removed) {
      state_removed = false;
      x_setempty(&states_used);
      for (state_no = 0; state_no <= no_states; state_no++) {
         for (sym = 1; sym <= last_nt; sym++) {
            actn = stripped_action_table(state_no, sym);
            if (action_type(actn) == SHIFT)
               x_set(&states_used, action_state(actn));
         }
      }

      for (state_no = 0; state_no <= no_states; state_no++) {
         if (!x_test(states_used, state_no)
             && accessing_symbol[state_no] !=0 ) {
            if (list_trace)
               printf("State %d became inaccessible\n", state_no);
            state_removed = true;
            accessing_symbol[state_no] = 0;
            for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
               action_table(state_no, t_sym) = phi_entry;
            }
         }
      }
   }
}

/*$PA  */
/*
               *********************************
               *                               *
               *         COMPUTE SETS          *
               *                               *
               *********************************
*/
void validate_table()
{
  /*  MAKES SURE TABLE IS CORRECT (INCOMPLETE TEST)  */
  table_state i;

  for (i = 1; i <= no_states; i++) {
      if (accessing_symbol[i] == 0) {
         sprintf(printbuffer, "state %d is inaccessible.", i);
         error(printbuffer, i);
      }
   }
}


void find_goal()
{
   /*  FIND THE GOAL SYMBOL  */
   table_state i;
   vocab_symbol j;
/* #### Page 6 */
   i = j = 0;

   find_action(action_pair(false, ACCEPT_STATE, 0), &i, &j);
   if (i < 0) {
      error("no accept state found", 1);
      return;
   }
   goal_symbol = accessing_symbol[i];
}
void compute_goto_set(nt_sym)
vocab_symbol nt_sym;
{
   /*  COMPUTE THE CONVENTIONAL GOTO SET  */

   table_state state_no;
   table_entry tab_entry;
   action table_action;
   set_of_states gt_set = NULLBITS;

   x_setempty(&gt_set);
   for (state_no = 0; state_no <= no_states; state_no++) {
      tab_entry = stripped_action_table(state_no, nt_sym);
      table_action = action_type(tab_entry);
      if (table_action == GOTO) {
         x_set(&gt_set, state_no);
      }
   }
   goto_set[nt_sym] = gt_set;
   gt_set = NULLBITS; /* don't free; we saved it */
}

boolean compute_lgtf(ss, nt_sym, lgtf)
vocab_symbol nt_sym;
set_of_states ss;
set_of_syms *lgtf;
{
   /*  COMPUTE LIMITED GOTO FOLLOW FOR A GIVEN START SET  */
   table_state j;
   vocab_symbol k;
   action actn;

   table_state goto_state;
   boolean found;
   found = false;
   x_setempty(lgtf);
   for (j = 0; j <= no_states; j++) {
      if (x_test(ss, j)) {
         goto_state = stripped_action_table(j, nt_sym);
         if (action_type(goto_state) == SHIFT) {
            goto_state = action_state(goto_state);
            found = true;
            for (k = 1; k <= no_terminals; k++) {
               actn = action_type(stripped_action_table(goto_state, k));
               if (actn != PHI) x_set(lgtf, k);
            }
/* #### Page 7 */
         }
      }
   }
   return found;
}

boolean find_reduces(rule_x, p, rf)
rule_no rule_x;
set_of_states *p;
set_of_syms *rf;
{
   /*  THIS PROCEDURE FINDS P(RULE_X,1) AND RF(RULE_X).  IF NO OCCURRENCES OF
   RED ARE FOUND IT RETURNS FALSE  */

   boolean found;
   table_entry actn_entry;
   vocab_symbol symbol;
   table_state state_no;

   actn_entry = action_pair(false, REDUCE, rule_x);     /*  THE TARGET  */
   state_no = 0;
   x_setempty(rf);
   x_setempty(p);
   found = false;
   symbol = 0;
   while (forever) {
      find_action(actn_entry, &state_no, &symbol);
      if (state_no < 0) break;
      x_set(p, state_no);
      x_set(rf, symbol);
      found = true;
      symbol = symbol + 1;
   }
   return found;
}
void inc_prod_array_ptr()
{
   if (prod_array_ptr < MAX_NO_PROD_SYMBOLS)
        prod_array_ptr = prod_array_ptr + 1;
   else {
      error("the grammar is too large", 2);
      prod_array_ptr = MAX_NO_PROD_SYMBOLS - 10;
   }
}

table_state new_row_number()
{
   no_states = no_states + 1;
   return no_states;
}

/* **********************
rule_no new_reduce_number(len, plh_set)
int len;
set_of_syms plh_set;
/* #### Page 8 ?/
{
   no_prods = no_prods + 1;
   rhs_len[no_prods] = len;
   plh[no_prods] = plh_set;
   return no_prods;
}
 ***************************** */

vocab_symbol create_new_nt()
{
   no_nts = no_nts + 1;
   return last_nt;
}

char *name_new_nt(numb, name)
char *name;
vocab_symbol numb;
{
   /*  NAME, IF PRESENT, SPECIFIES THE NEW NAME  */
   char *new_name;
   char buffer[10];

   sprintf(buffer,"<%d>",numb - no_terminals);
   new_name = newstring(buffer);
   if (name != "") {
     v[numb] = name;
   }
   else {
     v[numb] = new_name;
   }
   return new_name;
}
void clear_row(row)
table_state row;
{

  vocab_symbol sym;
  table_entry actn;

  for (sym = 1; sym <= last_nt; sym++) {
      actn = stripped_action_table(row, sym);
      if (action_type(actn) == REDUCE)
         x_reset(&reduce_set[action_rule(actn)], row);
      action_table(row, sym) = phi_entry;
   }
  accessing_symbol[row] = 0;
}

void copy_row(from_st, to_st)
table_state from_st, to_st;
{
   production_ptr prod;
   table_entry k;
   vocab_symbol sym;

   for (sym = 1; sym <= last_nt; sym++) {
      k = stripped_action_table(from_st, sym);
      action_table(to_st, sym) = k;
      if (action_type(k) == REDUCE) x_set(&reduce_set[action_rule(k)], to_st);
  }
   accessing_symbol[to_st] = accessing_symbol[from_st];
}

void move_row(from_st, to_st)
 table_state from_st, to_st;
{
/* #### Page 17 */
   vocab_symbol sym;
   table_entry actn_a, actn_b;
   table_state state_no;

   sym = accessing_symbol[from_st];
   copy_row(from_st, to_st);
   actn_a = action_pair(false, SHIFT, from_st);
   actn_b = action_pair(false, SHIFT, to_st);
   for (state_no = 0; state_no <= no_states; state_no++) {
      if (stripped_action_table(state_no, sym) == actn_a)
         action_table(state_no, sym) = actn_b;
   }
   clear_row(from_st);
   if (control[lt])printf("Row %d was moved to %d.\n", from_st, to_st);
}
/* $PA */

/*               **********************************
                 *                                *
                 *       GRAMMAR REDUCTION        *
                 *                                *
                 **********************************
*/


   boolean slr_1_ok(rule)
   rule_no rule;
   {
   /*  CHECKS IF THIS IS OK TO DROP FOR A SLRi GRAMMAR  */
   rule_no rule_1;
   vocab_symbol lhs;
   production_symbols_ptr ptr;
   vocab_symbol rhs;

      if (!control[sl]) return true;
      /*  IF THIS IS THE ONLY OCCURENCE OF THE LHS, OK IT  */
      lhs = prod_array[prod_start[rule]];
      for (rule_1 = 1; rule_1 <= no_prods; rule_1++) {
         if (rule_1 != rule && prod_array[prod_start[rule_1]] == lhs) {
            goto no_other_found;
         }
      }
      return true;

      no_other_found:

      rhs = prod_array[prod_start[rule] + 1];
      for (rule_1 = 1; rule_1 <= no_prods; rule_1++) {
         if (rule_1 != rule) {
            for (ptr = prod_start[rule_1] + 1;
                 ptr <= prod_start[rule_1] + rhs_len[rule_1]; ptr++) {
               if (prod_array[ptr] == rhs) goto non_trivial_rule;
            }
         }
/* #### Page 18 */
      }
      return true;

      non_trivial_rule:

      return false;
   }

boolean find_chain_rule(rule_x)
rule_no *rule_x;
{
   rule_no rule;
   production_symbols_ptr ps;
   /*  CHECK FOR PREFERRED FIRST; WE KNOW THEY ARE CHAIN RULES  */
   if (!x_empty(preferred_rules)) {
      for (rule = 1; rule <= no_prods; rule++) {
         if (x_test(preferred_rules, rule) && slr_1_ok(rule)) {
             *rule_x = rule;
             return true;
         }
      }
   }

   for (rule = 1; rule <= no_prods; rule++) {
       if (!x_test(lr_k_essential, rule)) {
          ps = prod_start[rule];
          if (ps > 0
              && rhs_len[rule] == 1
              && prod_array[ps + 1] >= first_nt
              && slr_1_ok(rule)) {
             *rule_x = rule;
             return true;
         }
      }
   }
   return false;
}

void substitute_in_grammar(nont_a, nont_b, new_nont)
vocab_symbol nont_a, nont_b, new_nont;
{
   production_symbols_ptr ptr;

   for (ptr = 1; ptr <= prod_array_ptr; ptr++) {
      if (prod_array[ptr] == nont_a || prod_array[ptr] == nont_b)
         prod_array[ptr] = new_nont;
   }
   if (goal_symbol == nont_a || goal_symbol == nont_b)
      goal_symbol = new_nont;
}
void combine_redundant_rules()
{
   rule_no rule_x, rule_y;
/* #### Page 19 */
   int i;
   table_state state_no;
   vocab_symbol t_sym;
   int ps_x, ps_y;
   table_entry old_actn, new_actn;
   for (rule_x = 1; rule_x <= no_prods; rule_x++) {
      if (prod_start[rule_x] != 0) {
         for (rule_y = rule_x + 1; rule_y <= no_prods; rule_y++) {
         if (prod_start[rule_y] != 0 && rhs_len[rule_x] != 0
            /* epsilon rule seems suspicious here; what did I intend? */
            && rhs_len[rule_x] == rhs_len[rule_y]) {
            ps_x = prod_start[rule_x];
            ps_y = prod_start[rule_y];
            for (i = 0; i <= rhs_len[rule_x]; i++) {
               if (prod_array[ps_x + i] != prod_array[ps_y + i])
                  goto cant_combine;
            }
            /*  THEY ARE THE SAME  */;
            if (list_trace) {
               printf("Rules %d and %d are redundant, rule %d discarded.\n",
               rule_x,rule_y,rule_y);
            }
            prod_start[rule_y] = 0;
            old_actn = action_pair(false, REDUCE, rule_y);
            new_actn = action_pair(false, REDUCE, rule_x);
            for (state_no = 0; state_no <= no_states; state_no++) {
               if (x_test(reduce_set[rule_y], state_no)) {
                  for (t_sym = 1; t_sym <= no_terminals; t_sym++) {
                     if (stripped_action_table(state_no, t_sym) == old_actn)
                        action_table(state_no, t_sym) = new_actn;
                  }
               }
            }
            x_or(&reduce_set[rule_x],reduce_set[rule_x], reduce_set[rule_y]);
            x_setempty(&reduce_set[rule_y]);
         }
         cant_combine:;
      }
      }
   }
}
/* $PA */
/*
                 **********************************
                 *                                *
                 *       COMBINE REDUCES          *
                 *                                *
                 **********************************
*/

table_state error_state;

   boolean cr(accessing_set, sym_b, rule_x)
   set_of_states accessing_set;
/* #### Page 20 */
   vocab_symbol sym_b;
   rule_no rule_x;
   {
      /*  ACTUALLY IMPLEMENTS COMBINE_REDUCES  */

      vocab_symbol lhs_x;
      table_state state_no;
      set_of_states g = NULLBITS;
      table_entry actn;
      table_state goto_state;
      boolean l;
      int i;
      vocab_symbol sym;
      boolean result;
      set_of_states g_minus_1 = NULLBITS, used = NULLBITS;
      set_of_states t_g = NULLBITS;
      {
         /*  ACCESSING SET IS_THE SET OF STATES WHICH SHIFT TO THE REDUCE ENTRY
         WE ARE WORKING ON.  IT IS USUALLY A PROPER SUBESET OF ALL THE SHIFTS
         TO THAT STATE, AND WE TRACE BACK FROM THAT SET RATHER FROM THE REDUCE
         ITSELF, THUS THE -1 BELOW  */

         /*  IF NO ITERATIONS, USE G_MINUS_1 DIRECTLY  */

         g = newbits(accessing_set);
         g_minus_1 = newbits(accessing_set);
         i = rhs_len[rule_x] - 1;
         while (i > 0) {
            x_setempty(&g_minus_1);
            x_setempty(&used);
            sym = prod_array[prod_start[rule_x] + i];
            for (state_no = 0; state_no <= no_states; state_no++) {
               actn = stripped_action_table(state_no, sym);
               if (action_type(actn) == SHIFT && x_test(g, action_state(actn))) {
                  x_set(&g_minus_1, state_no);
                  x_set(&used, action_state(actn));
               }
            }
            if (x_empty(g_minus_1) || (x_minus(&t_g, g, used),!x_empty(t_g))) {
               /* caution comma operator above */
               if (control[lt])
                  printf("Set g could not be found for rule %d.\n",rule_x);
               result = false;
               goto done;
            }
            freebits(&t_g);
            freebits(&g);
            g = newbits(g_minus_1);
            i = i - 1;
         }
         /*  WE HAVE THE RESTRICTED START SET. CHECK THAT THERE IS AN ERROR

         WHERE NEEDED IN EACH ROW IN THE LHS-SUCCESSOR OF RULE X  */;
         lhs_x = prod_array[prod_start[rule_x]];
         for (state_no = 0; state_no <= no_states; state_no++) {
/* #### Page 21 */
            actn = stripped_action_table(state_no, lhs_x);
            if (x_test(g, state_no)) {

               switch (action_type(actn)) {
               case SHIFT:

                  goto_state = action_state(actn);
                  switch (action_type(stripped_action_table(goto_state,sym_b))) {
                  case PHI:
                     action_table(goto_state, sym_b) = error_entry;
                     break;
                  case ESSENTIAL_ERROR:
                     /*  NOTHING  */;
                     break;
                  case REDUCE:
                     x_setempty(&t_g);
                     x_set(&t_g, state_no);
                     l = cr(t_g, sym_b,
                        action_rule(stripped_action_table(goto_state, sym_b)));
                     freebits(&t_g);
                     if (!l) {
                        result = false;
                        goto done;
                     }
                     break;
                  default:
                     printf("An essential error could not be put at (%d,%d).\n",
                        goto_state,sym_b);
                     result = false;
                     goto done;
                  }
                  break;
               case PHI:
                  /*  NO SUCCESSOR, USE A NEW STATE; CREATE IT IF NECESSARY  */
                  if (error_state == - 1) {
                     error_state = new_row_number();
                     for (sym = 1; sym <= no_terminals; sym++) {
                        action_table(error_state, sym) = phi_entry;
                     }
                     action_table(error_state, sym_b) = error_entry;
                     accessing_symbol[error_state] = lhs_x;
                  }
                  action_table(state_no, lhs_x)
                     = action_pair(false, SHIFT, error_state);
                  break;
               default:
                  sprintf(printbuffer, "ill formed table at (%d,%d)", state_no, lhs_x);
                  error(printbuffer, 2);
               }
            }
         }
         result = true;
      }
      done:
      freebits(&g);
/* #### Page 22 */
      freebits(&g_minus_1);
      freebits(&used);
      freebits(&t_g);
      return result;
   }

boolean combine_reduces(state_p, sym_b, rule_x)
table_state state_p;
vocab_symbol sym_b;
rule_no rule_x;
{
   /*  SEES IF THE ERROR ENTRY AT (STATE_P,SYM_B) CAN BE CHANGED TO RX */
   set_of_states accessing_set = NULLBITS;
   table_entry actn;
   vocab_symbol sym;
   table_state state_no;
   boolean l;

   error_state = - 1;
   /*  CALCULATE THE INITIAL ACCESSING SET.  ON THE FIRST CALL WE DON'T HAVE AN
   ACCESSING SET AS USED ABOVE, RATHER ALL ACCESSING ROWS COUNT  */

   sym = accessing_symbol[state_p];
   x_setempty(&accessing_set);
   for (state_no = 0; state_no <= no_states; state_no++) {
      actn = stripped_action_table(state_no, sym);
      if (action_type(actn) == SHIFT && action_state(actn) == state_p)
         x_set(&accessing_set, state_no);
   }

   l = cr(accessing_set, sym_b, rule_x);

   freebits(&accessing_set);

   return l;
}

/* $PA */
/*
                 **********************************
                 *                                *
                 *        COMBINE ROWS            *
                 *                                *
                 **********************************
*/
#define MAX_DEPTH 10

set_of_states combi_list[MAX_DEPTH];
int combi_list_max;
boolean c_row(state_p, state_q, ign_actn, state_r)
table_state state_p, state_q;
table_entry ign_actn;   /*  ACTION TO IGNORE  */
table_state state_r;    /*  THE ROW TO COMBINE INTO  */
{
/* #### Page 23 */
      /*  COMBINES TWO ROWS, IF POSSIBLE; RETURNS TRUE ON SUCCESS  */

   table_state state_no;
   table_state new_p, new_q, new_r;
   vocab_symbol sym;

   boolean l;
   set_of_states this_pair = NULLBITS;
   int i;
   boolean result;
   table_entry actn_p, actn_q, new_actn;
   table_entry actn;

         for (sym = 1; sym <= last_nt; sym++) {

            /*  FIRST TEST IF CAN THE ACTIONS BE COMBINED, BUT DOING NOTHING  */
            actn_p = stripped_action_table(state_p, sym);
            actn_q = stripped_action_table(state_q, sym);

            if (actn_p == ign_actn) actn_p = phi_entry;
            if (actn_q == ign_actn) actn_q = phi_entry;

            if (actn_p == actn_q)       /*   NOTHING  */;
            else if (actn_p == phi_entry)        /*  NOTHING  */;
            else if (actn_q == phi_entry)        /*  NOTHING  */;
            else if (action_type(actn_p) == SHIFT
                  && action_type(actn_q) == SHIFT) {
               /*  SHIFT/SHIFT... USE RECURSTVE CALL BUT DON'T BOTHER IF THEY
               ARE ALREADY BEING COMBINED  */
               new_p = action_state(actn_p);
               new_q = action_state(actn_q);
               x_setempty(&this_pair);
               x_set(&this_pair, new_q);
                  for (i = 0; i <= combi_list_max; i++) {
                     if (combi_list[i] == this_pair) goto done_with_check;
                  }
                  combi_list_max = combi_list_max + 1;
                  if (combi_list_max >= MAX_DEPTH) {
                        error("state combination 1ist overflowed",2);
                  }
                  combi_list[combi_list_max] = this_pair;
                  this_pair = NULLBITS;
                  new_r = min(new_p, new_q);
                  if (!c_row(new_p,new_q,phi_entry, new_r)) {
                     result = false;
                     goto done;
                  }
                  /*  WE HAVE SUCCESSFULLY COMBINED THE ROWS, NOW UPDATE THE
                  TABLE TO REFLECT THIS  */
                  new_actn = action_pair(false, SHIFT, new_r);
                  for (state_no = 0; state_no <= no_states; state_no++) {
                     actn = stripped_action_table(state_no, sym);
                     if (action_type(actn) == SHIFT
                        && (action_state(actn) == new_p || action_state(actn) == new_q)) {
/* #### Page 24 */
                        action_table(state_no, sym) = new_actn;
                     }
                  }

                  if (new_p != new_r) clear_row(new_p);
                  if (new_q != new_r) clear_row(new_q);
                  combi_list_max = combi_list_max - 1;
                  freebits(&combi_list[combi_list_max]);

                  /*  AT THIS POINT WE ASSERT THAT THE ACTIONS BEING COMBINED
                  ABOVE ARE THE SAME AND POINT TO A COMBINED ROW_R. NEW_P AND
                  NEW_Q HAVE BEEN DISCARDED.   IF IN A SUBSEQUENT RECURSTON, THE
                  COMBINED ROW IS THEN COMBINED WITH A THIRD ROW, BOTH ENTRIES
                  WILL BE CHANGED TO POINT TO THE RESULT OF THE ADDITIONAL
                  COMBINATION, AND STILL BE CORRECT.  */

               done_with_check:;
               /*  AT THIS POINT EITHER THE ASSERTION ABOVE HOLDS OR THE STATES
               ARE BEING COMBINED IN AN EARLIER ITERATION. WE CAN USE EITHER
               ENTRY IN THIS CASE, AND THE IT WILL BE CHANGED WHEN THE EARLIER
               COMBINATION IS COMPLETED  */
            }

            /*else if (action_type(actn_p) == REDUCE      DT 11/21 */
            else if ((action_type(actn_p) == REDUCE || action_type(actn_p) == ACCEPT_STATE)
                  && action_type(actn_q) == ESSENTIAL_ERROR) {
               l = combine_reduces(state_q, sym, action_rule(actn_p));
               if (!l) {
                  result = false;
                  if (control[lt]) {
                     printf("Rows %d and %d are incompatible for symbol %s\n",
                     state_p,state_q,v[sym]);
                  }
                  goto done;
               }
            }

            /*else if (action_type(actn_q) == REDUCE &&     DT 11/21 */
            else if ((action_type(actn_q) == REDUCE || action_type(actn_q) == ACCEPT_STATE)
                  && action_type(actn_p) == ESSENTIAL_ERROR) {
               l = combine_reduces(state_p, sym, action_rule(actn_q));
               if (!l) {
                  result = false;
                  if (control[lt]) {
                     printf("Rows %d and %d are incompatible for symbol %s\n",
                     state_q,state_p, v[sym]);
                  }
                  goto done;
               }
            }
            else {
               result = false;
               if (control[it]) {
                  printf("Rows %d and %d are incompatible for symbol %s\n",
                     state_q,state_p,v[sym]);
                  }
               goto done;
/* #### Page 25 */
            }
         }

         if (list_trace) {
            printf("Rows %d and %d were compatibly combined as %d\n",
               state_p,state_q,state_r);
         }

         /*  NOW WE KNOW WE CAN COMBINE THE ROWS, DO IT FOR REAL  */
         accessing_symbol[state_r] = accessing_symbol[state_p];

         for (sym = 1; sym <= last_nt; sym++) {
            action_table(state_r, sym) = phi_entry;
            actn_p = stripped_action_table(state_p, sym);
            actn_q = stripped_action_table(state_q, sym);
            if (actn_p == ign_actn) actn_p = phi_entry;
            if (actn_q == ign_actn) actn_q = phi_entry;
            if (action_type(actn_p) == REDUCE)
               x_set(&reduce_set[action_rule(actn_p)], state_r);
            if (action_type(actn_q) == REDUCE)
               x_set(&reduce_set[action_rule(actn_q)], state_r);
            if (actn_p == actn_q) {
               action_table(state_r, sym) = actn_p;
            }
            else if (actn_p == phi_entry) {
               action_table(state_r, sym) = actn_q;
            }
            else if (actn_q == phi_entry) {
               action_table(state_r, sym) = actn_p;
            }
            else if (action_type(actn_p) == SHIFT
                  && action_type(actn_q) == SHIFT) {
               /*  THEY MUST BE GOING TO BE COMBINED LATER  */
               action_table(state_r, sym) = actn_p; /*  OR Q, EITHER ONE  */
            }
            /*else if (action_type(actn_p) == REDUCE   DT 11/21 */
            else if ((action_type(actn_p) == REDUCE || action_type(actn_p) == ACCEPT_STATE)
                  && action_type(actn_q) == ESSENTIAL_ERROR) {
               action_table(state_r, sym) = actn_p;
            }
            /*else if (action_type(actn_q) == REDUCE   DT 11/21 */
            else if ((action_type(actn_q) == REDUCE || action_type(actn_q) == ACCEPT_STATE)
                  && action_type(actn_p) == ESSENTIAL_ERROR) {
               action_table(state_r, sym) = actn_q;
            }
            else {
               /*  OOPS, THERE AREN"T SUPPOSED TO BE ANY OF THESE  */
               sprintf(printbuffer, " inconsistent entries at %d and %d for %s",
                  state_p, state_q, v[sym]);
               error(printbuffer, 2);
            }
         }
         result = true;
      done:

      freebits(&this_pair);
      return result;
}
/* #### Page 26 */
boolean combine_rows(s_p, s_q, i_a, s_r)
table_state s_p, s_q;
table_entry i_a;        /*   ACTION TO IGNORE  */
table_state s_r;        /*   THE ROW TO COMBINE INTO  */
{
   boolean l;
   int i;

   for (i=0; i<MAX_DEPTH;i++) {
      combi_list[i] = NULLBITS;
   }

   combi_list_max = - 1;
   l = c_row(s_p, s_q, i_a, s_r);

   for (i=0; i<MAX_DEPTH;i++) {
      freebits(&combi_list[i]);
   }

   return l;
}

/* $PA */
/*
                 **********************************
                 *                                *
                 *         COMBINE_COLUMNS        *
                 *                                *
                 **********************************
*/
boolean combine_columns(nont_a, nont_b, new_nont, rule)
vocab_symbol nont_a, nont_b, new_nont;
rule_no rule;
{
   table_entry k;
   table_state new_row;
   table_state state_no, state_2;
   table_state a_state, b_state;
   table_entry actn_a, actn_b, new_actn;

#define COMBI_MAX 15
   int i;
   int no_combi;
   table_state combi_from[COMBI_MAX], combi_to[COMBI_MAX];

   no_combi = 0;

   for (state_no = 0; state_no <= no_states; state_no++) {
      action_table(state_no, new_nont) = phi_entry;
   }

   for (state_no = 0; state_no <= no_states; state_no++) {
      actn_a = stripped_action_table(state_no, nont_a);
      actn_b = stripped_action_table(state_no, nont_b);
/* #### Page 27 */
      if (actn_a == actn_b) {
         /*  THIS COMES FROM A PREVIOUS COMBINATION OF THE SAME PAIR (ABOUT 20
         LINES BELOW) AND CAN SIMPLY BE IGNORED EXCEPT TO CLEAR THE ENTRIES.  */
         action_table(state_no, nont_a) = phi_entry;
         action_table(state_no, nont_b) = phi_entry;
      }
      else if (actn_a == phi_entry) {
         action_table(state_no, nont_b) = phi_entry;
         action_table(state_no, new_nont) = actn_b;
         accessing_symbol[action_state(actn_b)] = new_nont;
      }
      else if (actn_b == phi_entry) {
         action_table(state_no, nont_a) = phi_entry;
         action_table(state_no, new_nont) = actn_a;
         accessing_symbol[action_state(actn_a)] = new_nont;
      }
      else {
         new_row = new_row_number();
         a_state = action_state(actn_a);
         b_state = action_state(actn_b);
         if (no_combi <= COMBI_MAX) {
            /*  B_STATE SHOULD CONTAIN THE CHAIN RULE SO USE A  */
            combi_from[no_combi] = a_state;
            combi_to[no_combi] = new_row;
            no_combi = no_combi + 1;
         }
         if (combine_rows(a_state, b_state, action_pair(false, REDUCE, rule), new_row)) {
            new_actn = action_pair(false, SHIFT, new_row);
            action_table(state_no, new_nont) = new_actn;
            action_table(state_no, nont_a) = phi_entry;
            action_table(state_no, nont_b) = phi_entry;
            accessing_symbol [new_row] = new_nont;
            for (state_2 = state_no + 1; state_2 <= no_states; state_2++) {
               if (stripped_action_table(state_2, nont_a) == actn_a
                && stripped_action_table(state_2, nont_b) == actn_b) {
                  action_table(state_2, nont_a) = new_actn;
                  action_table(state_2, nont_b) = new_actn;
                  action_table(state_2, new_nont) = new_actn;
               }
            }
         }
         else {
            return false;
         }
      }
   }
   for (state_no = 0; state_no <= no_states; state_no++) {
      if (accessing_symbol[state_no] == nont_a
       || accessing_symbol[state_no] == nont_b)
          clear_row(state_no);
   }
   /*  NOW MOVE THE ROWS BACK WHERE THEY CAME FROM (TO MINIMISE SPREAD OUT)  */
   for (i = 0; i <= no_combi - 1; i++) {
      /*  BE SURE IT"S SAFE FIRST  */
/* #### Page 28 */
      if (accessing_symbol[combi_from[i]] == 0)
         move_row(combi_to[i], combi_from[i]);
   }
   return true;
}

/* $PA */
/*
                 **********************************
                 *                                *
                 *    ELIMINATE_IDENTICAL ROWS    *
                 *                                *
                 **********************************
*/

   void compare_and_combine(state_1, state_2, changed, state_changed)
   table_state state_1, state_2;
   boolean *changed;
   set_of_states *state_changed;
   {
      table_state state_3;
      vocab_symbol sym;
      table_entry actn_1, actn_2;
      vocab_symbol acc_sym;
      /*  DOES THE DIRTY WORK, NEXT PROCEDURE DOES ELIGIBILITY  */
      if (accessing_symbol[state_1] == accessing_symbol[state_2]) {
         for (sym = 1; sym <= last_nt; sym++) {
            actn_1 = stripped_action_table(state_1, sym);
            if (actn_1 != stripped_action_table(state_2, sym)) {
               return;
            }
         }
         if (list_trace)
            printf("Identical states %d and %d were combined into %d.\n",
               state_1,state_2,state_1);
         *changed = true;
         actn_1 = action_pair(false, SHIFT, state_1);
         actn_2 = action_pair(false, SHIFT, state_2);
         acc_sym = accessing_symbol[state_1];
         for (state_3 = 0; state_3 <= no_states; state_3++) {
            if (stripped_action_table(state_3, acc_sym) == actn_1
             || stripped_action_table(state_3, acc_sym) == actn_2) {
               /*  TEST BOTH FOR STATE_TESTED LOGIC  */
               action_table(state_3, acc_sym) = actn_1;
               x_set(state_changed, state_3);
            }
         }
         clear_row(state_2);
      }
   }

void eliminate_identical_rows()
{
   /*  FIND AND COMBINE ALL IDENTICAL ROWS  */
   set_of_states state_tested = NULLBITS, state_changed = NULLBITS;
/* #### Page 29 */
   boolean changed;
   table_state state_1, state_2;

   changed = false;

   x_setempty(&state_tested);
   x_setempty(&state_changed);
   for (state_1 = 0; state_1 <= no_states; state_1++) {
      if (accessing_symbol[state_1] != 0) {
         for (state_2 = state_1 + 1; state_2 <= no_states; state_2++) {
            compare_and_combine(state_1, state_2, &changed, &state_changed);
         }
         x_set(&state_tested, state_1);
      }
   }

   x_minus(&state_tested,state_tested, state_changed);

   while (changed) {
      changed = false;
      x_setempty(&state_changed);
      for (state_1 = 0; state_1 <= no_states; state_1++) {
         if (accessing_symbol[state_1] != 0 && !x_test(state_tested, state_1)) {
            for (state_2 = 0; state_2 <= no_states; state_2++) {
                if (state_1 != state_2) compare_and_combine(state_1, state_2,
                        &changed, &state_changed);
             }
         }
         x_set(&state_tested, state_1);
      }
      x_minus(&state_tested,state_tested, state_changed);
   }
}


   int combine_pair(nont_a, nont_b)
   vocab_symbol nont_a, nont_b;
   {
      /*  TESTS TO SEE IF NONT_A AND NONT_B CAN BE COMBINED;
      RESULTS: O = NEVER COMBINABLE.
               1 = POSSIBLY, BUT NOT YET
               2 = CAN BE COMBINED.  */

#define NO_RULES_OF_NT 20
      rule_no a_rules[NO_RULES_OF_NT];
      rule_no b_rules[NO_RULES_OF_NT];
      rule_no prod_no;
      int a_ptr, b_ptr;
      int i, j, k, temp;
      boolean exact_match, match_found, combinable_now;
      vocab_symbol sym_a, sym_b;
      vocab_symbol sym;
      table_state state_1, state_2;
      table_state state_no;
/* #### Page 30 */
      /*  FIRST COMPARE THE GOTO SETS  */
      state_1 = - 1;
      state_2 = - 2;
      for (state_no = 0; state_no <= no_states; state_no++) {
         if (action_type(stripped_action_table(state_no, nont_a)) != PHI)
            state_1 = state_no;
         if (action_type(stripped_action_table(state_no, nont_b)) != PHI)
            state_2 = state_no;
         if (state_1 == state_2) return 0;
      }
      /*  GOTO SETS ARE DISJOINT  */

      /*  NOW GET THE RULES AND COMPARE THEM  */
      a_ptr = b_ptr = 0;
      for (prod_no = 1; prod_no <= no_prods; prod_no++) {
         if (prod_array[prod_start[prod_no]] == nont_a) {
            if (a_ptr > NO_RULES_OF_NT) {
               sprintf(printbuffer, "too many rhs's for %s", v[nont_a]);
               error(printbuffer, i);
               a_ptr = a_ptr - 1;
            }
            a_rules[a_ptr] = prod_no;
            a_ptr = a_ptr + 1;
         }
         if (prod_array[prod_start[prod_no]] == nont_b) {
            if (b_ptr > NO_RULES_OF_NT) {
               sprintf(printbuffer, "too many rhs's for %s", v[nont_b]);
               error(printbuffer, i);
               b_ptr = b_ptr - 1;
            }
            b_rules[b_ptr] = prod_no;
            b_ptr = b_ptr + 1;
         }
      }
      if (control[sl] && a_ptr != b_ptr) return 1;
      /*  MAKE SURE THAT NONT_A HAS THE LARGER NUMBER OF RULES (IF DIFFERNET)*/
      a_ptr = a_ptr - 1;
      b_ptr = b_ptr - 1;
      if (b_ptr > a_ptr) {
         for (i = 0; i <= b_ptr; i++) {
            temp = a_rules[i];
            a_rules[i] = b_rules[i];
            b_rules[i] = temp;
         }
         temp = b_ptr;
         b_ptr = a_ptr;
         a_ptr = temp;
         temp = nont_b;
         nont_b = nont_a;
         nont_a = temp;
      }

     /*   SLR(1) REQUIRES THAT THE GOTO FOLLOWS BE THE SAME  */
     if (control [sl]) {
         state_1 = action_state(stripped_action_table(state_1, nont_a));
/* #### Page 31 */
         state_2 = action_state(stripped_action_table(state_2, nont_b));
         for (sym = 1; sym <= no_terminals; sym++) {
            if (action_type(stripped_action_table(state_1, sym)) == PHI
             && action_type(stripped_action_table(state_2, sym)) != PHI) return 0;
            if (action_type(stripped_action_table(state_2, sym)) == PHI
             && action_type(stripped_action_table(state_1, sym)) != PHI) return 0;
         }
      }

      combinable_now = true;
      for (i = 0; i <= a_ptr; i++) {
         match_found = false;
         {
            for (j = 0; j <= b_ptr; j++) {
               exact_match = false;
               if (rhs_len[a_rules[i]] == rhs_len[b_rules[j]]) {
                  exact_match = true;
                  for (k = 0; k <= rhs_len[a_rules[i]]; k++) {
                     sym_a = prod_array[prod_start[a_rules[i]] + k];
                     sym_b = prod_array[prod_start[b_rules[j]] + k];
                     if (sym_a == nont_a) sym_a = nont_b;
                     if (sym_b == nont_a) sym_b = nont_b;
                     if (sym_a != sym_b) {
                        exact_match = false;
                        if (sym_a < first_nt) goto scan_done;
                        if (sym_b < first_nt) goto scan_done;
                     }
                  }
                  match_found = true;
                  if (exact_match) goto found_a_match;
               }
               scan_done:;
            }
            if (!match_found) return 0;
         }
         found_a_match:
         /*  HERE I AND J MATCH, AT LEAST MODULO THE NON-T'S  */
         if (!exact_match) combinable_now = false;
      }

      if (combinable_now) return 2;
      return 1;
   }

void combine_disjoint()
{
/* PROCEDURE TO COMBINE THOSE DISJOINT COLUMNS WHICH CAN BE COMBINED */
  vocab_symbol nont_a, nont_b;
  table_state state_no;
  table_entry k;

  for (nont_a = first_nt; nont_a <= last_nt; nont_a++) {
      if (v[nont_a] != deleted_nont) {
      for (nont_b = nont_a + 1; nont_b <=last_nt; nont_b++) {
         if (v[nont_b] != deleted_nont &&
/* #### Page 32 */
            !x_test(nt_uncombinable[nont_a], nont_b)) {
            switch (combine_pair(nont_a, nont_b)) {
            case 0:     /*  0: NEVER COMBINABLE  */
               x_set(&nt_uncombinable[nont_a], nont_b);
               x_set(&nt_uncombinable[nont_b], nont_a);
               break;
            case 1:     /*  1: MAYBE LATER  */
               break;
            case 2:     /*  2: CAN DO NOW  */
               if (control[sd])
                  printf("Disjoint columns for %s and %s were combined\n",
                  v[nont_a],v[nont_b]);
               substitute_in_grammar(nont_a, nont_b, nont_a);
               v[nont_b] = deleted_nont;
               for (state_no = 0; state_no <= no_states; state_no++) {
                  k = stripped_action_table(state_no, nont_b);
                  if (action_type(k) != PHI)
                     action_table(state_no, nont_a) = k;
                  if (accessing_symbol[state_no] == nont_b)
                     accessing_symbol[state_no] = nont_a;
               }
               break;
            }
         }
         }
      }
   }
}

void eliminate_duplicate_reduces()
{
   table_state state_1, state_2, state_no;
   table_entry actn;
   table_state new_row;
   rule_no rule_x;

   for (rule_x = 1; rule_x <= no_prods; rule_x++) {
      for (state_1 = 0; state_1 <= no_states; state_1++) {
         if (x_test(reduce_set[rule_x], state_1)) {
            for (state_2 = state_1 + 1; state_2 <= no_states; state_2++) {
               if (x_test(reduce_set[rule_x], state_2)) {
                  backup();
                  new_row = min(state_1, state_2);
                  if (combine_rows(state_1, state_2, phi_entry, new_row)) {
                     if (list_trace)
                         printf("Duplicate occrrences of rule %d were combined above from state %d and %d into %d.\n",
                         rule_x,state_1,state_2,new_row);
                     x_reset(&reduce_set [rule_x], state_2);
                     for (state_no = 0; state_no <= no_states; state_no++) {
                        actn = stripped_action_table(state_no, accessing_symbol[state_1]);
                        if (action_type(actn) == SHIFT
                            && (action_state(actn) == state_1
                              || action_state(actn) == state_2))
                              action_table(state_no, accessing_symbol[state_1])
                                 = action_pair(false, SHIFT, new_row);
/* #### Page 33 */
                     }
                     clear_row(max(state_1, state_2));
                  }
                  else {
                     if (list_trace)
                        printf("An attempt to combine %d and %d into %d to eliminate duplicates of rule %d failed.\n",
                        state_1,state_2,new_row,rule_x);
                     restore();
                     if (rhs_len[rule_x] == 1
                         && prod_array[prod_start[rule_x] + 1] >= first_nt
                         && !x_test(lr_k_essential, rule_x)) {
                        /*  ITS A CHAIN RULE  */;
                        x_set(&preferred_rules, rule_x);
                        goto rule_combined;
                     }
                  }
               }
            }
         }
      }
      rule_combined:;
   }
}


void housekeep()
{
   table_state state_no, max_used;
   production_symbols_ptr g_sym;
   boolean changed;
   vocab_symbol sym, sym_1;
   table_entry k;
   max_used = 1;
   for (state_no = 1; state_no <= no_states; state_no++) {
      if (accessing_symbol[state_no] != 0) {
        if (max_used != state_no) move_row(state_no, max_used);
        max_used = max_used + 1;
      }
   }

   no_states = max_used - 1;
   changed = true;
   sym = first_nt;
   while (changed) {
      while (v[last_nt] == deleted_nont) {
         no_nts = no_nts - 1;
      }
      changed = false;
      for (sym = sym; sym <= last_nt; sym++) {
         if (v[sym] == deleted_nont) {
           if (goal_symbol == last_nt) goal_symbol = sym;
           for (state_no = 0; state_no <= no_states; state_no++) {
               action_table(state_no, sym) =
                  stripped_action_table(state_no, last_nt);
               if (accessing_symbol[state_no] == last_nt)
/* #### Page 34 */
                  accessing_symbol[state_no] = sym;
            }
            for (g_sym = 1; g_sym <=prod_array_ptr; g_sym++) {
               if (prod_array[g_sym] == last_nt) prod_array[g_sym] = sym;
            }
            nt_uncombinable[sym] = nt_uncombinable[last_nt];
            for (sym_1 = first_nt; sym_1 <= last_nt; sym_1++) {
               if (x_test(nt_uncombinable[sym_1], last_nt)) {
                  x_set(&nt_uncombinable[sym_1], sym);
                  x_reset(&nt_uncombinable[sym_1], last_nt);
               }
            }
            v[sym] = v[last_nt];
            no_nts = no_nts - 1;
            changed = true;
            break;
         }
      }
   }
}

void initialize()
{
   int rule_x;

   phi_entry = action_pair(false, PHI, 0);
   error_entry = action_pair(false, ESSENTIAL_ERROR, 0);
   for (rule_x = 1; rule_x <= MAX_NO_PRODS; rule_x++) {
      rhs_len[rule_x] = unspec_len;
      x_setempty(&plh[rule_x]);
   }
   if (control[it]) control[sd] = true;
   mso = fopen("cmptab.out","w");
}

/* $PA */
/*
             ***********************************
             *                                 *
             *             MAIN                *
             *                                 *
             ***********************************
*/
main(argc,argv)
int argc;
char **argv;
{
        vocab_symbol lhs_x, rhs_x;
        vocab_symbol old_last_nt;
        vocab_symbol new_nont;
        rule_no rule_x;
        setvbuf(stdout, NULL, _IONBF, 0); /* ?????????????????? */
        set_control(argc,argv);

        initialize();
/* #### Page 35 */
        read_table();

        validate_table();
        if (error_count > 0 && !control[ie]) abort();

        if (control[lf]) echo_table();

        list_trace = control[lf] && control[it];

        extract_grammar();
        find_goal();
        find_all_inaccessibles();
        check_lhs_use();

        x_setempty(&lr_k_essential);
        backup();
        restore();
        if (control[ap]) {
           echo_table();
           if (control[pt]) punch_table();
           print_g(true, control[pg]);
        }

        eliminate_duplicate_reduces();
        eliminate_identical_rows();
        housekeep();

        if (control[it]) {
           echo_table();
           if (control[pt]) punch_table();
           print_g(true, control[pg]);
        }

        list_trace = control[lt];
        old_last_nt = infinity;
        while (last_nt < old_last_nt) {
           old_last_nt = last_nt;
           combine_disjoint();
           combine_redundant_rules();
           eliminate_duplicate_reduces();
           eliminate_identical_rows();
           housekeep();
        }

        if (control[it]) {
           echo_table();
           if (control[pt]) punch_table();
           print_g(true, control[pg]);
        }

        if (!control[go]) {
           while (find_chain_rule(&rule_x)) {
                 x_setempty(&preferred_rules);
                 lhs_x = prod_array[prod_start[rule_x]];
/* #### Page 36 */
                 rhs_x = prod_array[prod_start[rule_x] + 1];
                 if (control[sd])
                    printf("Eliminating rule %d by combining %s and %s\n",
                    rule_x,v[lhs_x],v[rhs_x]);
                 backup();
                 new_nont = create_new_nt();
                 substitute_in_grammar(lhs_x, rhs_x, new_nont);
                 combine_redundant_rules();
                 eliminate_identical_rows();
                 if (!combine_columns(lhs_x, rhs_x, new_nont, rule_x)) {
                    restore();
                    x_set(&lr_k_essential, rule_x);
                    if (control[sd])
                       printf("Rule %d is essential, the combinations above are not used.\n",
                       rule_x);
                    continue;
                 }
                 name_new_nt(new_nont, v[lhs_x]);
                 v[rhs_x] = v[lhs_x] = deleted_nont;
                 prod_start[rule_x] = 0;
                 x_setempty (&reduce_set[rule_x]);
                 combine_disjoint();
                 combine_redundant_rules();
                 eliminate_duplicate_reduces();
                 eliminate_identical_rows();
                 housekeep();
                 if (control[it]) echo_table();

                 if (control[pt]) punch_table();
                 if (control[ig] || control[pg]) print_g(control[ig], control[pg]);
                 /*  WORK NEEDED HERE  */
            }

            old_last_nt = infinity;
            while (last_nt < old_last_nt) {
              old_last_nt = last_nt;
              combine_disjoint();
              combine_redundant_rules();
              eliminate_duplicate_reduces();
              eliminate_identical_rows();
              housekeep();
            }
            if (control[ft] && !control[it]) echo_table();
            if (control[pi] && !control[pt]) punch_table();
            print_g(control[fg], control[pf]);
         }
         if (control[ea]) eject_page;
         exit(0);
}
