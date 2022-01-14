/* #### Page 1 */
#include <stdio.h>
#include <string.h>

#include "type.h"
#include "utility.h"
#include "options.h"
#include "bitstring.h"
#include "symbol.h"
#include "grammar.h"
#include "table.h"
#include "tableio.h"
#include "extractg.h"

void find_rule(rule_no rule_x, set_of_syms *rf, set_of_states *start_set);
boolean find_right_part(rule_no rule_x, set_of_states p[], set_of_syms rf, bitstring trace_marks[2], int *position);
/*
                 *********************************
                 *                               *
                 *        EXTRACT GRAMMAR        *
                 *                               *
                 *********************************
*/

/*  RECOVER THE GRAMMAR FROM THE TABLE  */

#define SYMBOL_LIST_MAX 10
vocab_symbol symbol_list[SYMBOL_LIST_MAX];

void list_states(redn, position, trace_marks, x, title)
rule_no redn;
int position;
bitstring trace_marks[];
set_of_states x[];
char *title;
{
      /*  LISTS THE STATES FOUND DURING EACH REDUCTION STEP  */

      int i;
      table_state j;
      vocab_symbol symbol;

      printf("%s was used for reduction %d:\n", title, redn);
      for (i = 0; i <= position; i++) {
         symbol = symbol_list[i];
         if (x_test(trace_marks[0], i))
            printf("  >");
         else
            printf("   ");
         if (x_test(trace_marks[1], i))
            printf(">");
         else
            printf(" ");
         printf("%-10s ",v[symbol]);
         for (j = 0; j <= no_states; j++) {
            if (x_test(x[i], j)) printf("%3d",j);
         }
         printf("\n");
      }
   }

/* #### Page 2 */
boolean find_right_part(rule_no rule_x, set_of_states p[], set_of_syms rf, bitstring trace_marks[2], int *position)
{
      /*  THIS PROCEDURE FINDS THE RIGHT PART OF THE REDUCTION BY SEARCHING THE
      TABLE BACKWARDS FROM THE STATES DEFINED BY P(0)  */
      table_entry actn_entry;
      int markpos_0, markpos_1;
      int mark_position;
      boolean multi_mark;
      char *text, *text1;
      vocab_symbol symbol;
      int markcnt_0, markcnt_1;
      vocab_symbol sym, nt_sym;
      table_state state_to, state_from;
      set_of_states goto_presence;

      boolean result;

      text = text1 = NULL;
      markcnt_0 = markcnt_1 = 0;
      *position = 1;
      x_setempty(&trace_marks[0]);
      x_setempty(&trace_marks[1]);

      /*  CHECK FOR EMPTY RULE POSSIBILITY  */
      for (nt_sym = first_nt; nt_sym <= last_nt; nt_sym++) {
         goto_presence = NULLBITS;
/*       if (x_empty(plh[rule_x]) || x_test(plh[rule_x],nt_sym))  (Comment in XPL: translate to &&) */
         if (x_empty_minus(p[0], goto_set[nt_sym])
            && compute_lgtf(p[0], nt_sym, &goto_presence)
            && x_empty_minus(rf, goto_presence)) {
            markpos_0 = *position;
            markcnt_0 = markcnt_0 + 1;
            x_set(&trace_marks[0], 0);
            if (x_equal(p[0], goto_set[nt_sym])) {
               x_set(&trace_marks[1], 0);
               markpos_1 = *position;
               markcnt_1 = markcnt_1 + 1;
            }
         }
         freebits(&goto_presence);
      }

      /*  NOW BACK UP THRU THE TABLE  */
      while (forever) {
         symbol_list[*position] = 0;
         p[*position] = NULLBITS;
         x_setempty(&(p[*position]));
         for (state_to = 0; state_to <= no_states; state_to++) {
            /*  WHAT SET OF STATES GOT US INTO THIS SET  */
/* #### Page 3 */
            if (x_test(p[(*position) - 1], state_to)) {
               sym = accessing_symbol[state_to];

               if (sym == 0)
                  goto end_find_rhs;
               if (symbol_list[*position] == 0)
                  symbol_list[*position] = sym;
               else if (symbol_list[*position] != sym)
                  goto end_find_rhs;
               actn_entry = action_pair(false, SHIFT, state_to);
               state_from = 0;
               while (forever) {
                  find_action_in_col(actn_entry, &state_from, sym);
                  if (state_from < 0) break;
                  x_set(&p[*position], state_from);
                  state_from = state_from + 1;
               }
            }
         }

         /*  NOW CHECK THE GOTOS AS POSSIBLE LHSS  */
         for (nt_sym = first_nt; nt_sym <= last_nt; nt_sym++) {
            goto_presence = NULLBITS;
            if ((x_empty(plh[rule_x]) || x_test(plh[rule_x], nt_sym))
                && (*position != 1 || symbol_list[1] != nt_sym)
                && x_empty_minus(p[*position], goto_set[nt_sym])
                && compute_lgtf(p[*position], nt_sym, &goto_presence)
                && x_empty_minus(rf, goto_presence))  {
               x_set(&trace_marks[0], *position);
               if (x_equal(p[*position], goto_set[nt_sym]))
                   x_set(&trace_marks[1],*position);
               /* WE SHOULD ALSO TEST THE FOLLOW SETS HERE, BUT AS THIS IS THE
                  ONLY PLACE WE WOULD NEED THE GOTO FOLLOW, AND IT IS ONLY USED
                  FOR MARKING, WHICH IS ONLY INFORMATIVE AND NOT REQUIRED FOR
                  THE ALG, WE OMIT THE TEST.  THE EFFECT IS TO STRONGLY MARK
                  SOME POSITIONS WHICH WOULD OTHERWISE BE WEAKLY MARKED.  */
            }
            freebits(&goto_presence);
         }
         if (x_test(trace_marks[0], *position)) {
            /* WE SET IT (AT LEAST ONCE)  */
            markpos_0 = *position;
            markcnt_0 = markcnt_0 + 1;
         }
         if (x_test(trace_marks[1], *position)) {
            /* WE SET IT (AT LEAST ONCE)  */
            markpos_1 = *position;
            markcnt_1 = markcnt_1 + 1;
         }
         *position = *position + 1;
/* #### Page 4 */
      }

      end_find_rhs:

      /* WE NOW HAVE TRACED BACK AS FAR AS WE CAN, INSPECT THE MARKS TO SEE
         WHETHER THERE IS A PROPER MARK, AND CHOOSE THE STRONGEST POSSIBLE. THIS
         LOGIC IS IRRELEVENT IF THE LENGTH AND LHS ARE KNOWN, BUT NECCESSARY
         OTHERWISE.  */

      if (markcnt_0 == 0) {
         sprintf(printbuffer, "rule %d has no marks ", rule_x);
         error(printbuffer, 1);
         *position = *position - 1;
         if (list_trace) list_states(rule_x, *position, trace_marks, p, "no mark");
         result = false;
         goto exit_point;
      }
      else if (markcnt_1 > 1) {
         mark_position = markpos_1;
         multi_mark = true;
         text = "strong mark";
      }
      else if (markcnt_1 == 1) {
         mark_position = markpos_1;
         multi_mark = false;
         text = "strong mark";
      }
      else if (markcnt_0 > 1) {
         mark_position = markpos_0;
         multi_mark = true;
         text = "weak mark";
      }
      else if (markcnt_0 == 1) {
         mark_position = markpos_0;
         multi_mark = false;
         text = "weak mark";
      }

      text = newstring(text);
      if (rhs_len[rule_x] != unspec_len) {
         /*  WE KNOW THE LENGTH, VALIDATE  */
         text1 = "";
         if (x_test(trace_marks[0], rhs_len[rule_x])) {
            text1 = "confirmed by a weak mark";
            *position = rhs_len[rule_x];
         }
         if (x_test(trace_marks[1], rhs_len[rule_x])) {
            text1 = "confirmed by a strong mark";
            *position = rhs_len[rule_x];
         }
         if (strlen(text1) == 0) {
            if (!multi_mark) {
                sprintf(printbuffer, "refigured from a %s", text);
                text1 = printbuffer;
            }
            else {
               sprintf(printbuffer, "was refigured from the leftmost %s", text);
/* #### Page 5 */
               text1 = printbuffer;
            }
            *position = mark_position;
         }
         text1 = newstring(text1);
         if (rhs_len[rule_x] != *position) {
            sprintf(printbuffer,
               "the length of rule %d was changed from %d to %d",
               rule_x, rhs_len[rule_x], *position);
            error(printbuffer,      1);
         }
         if (list_trace) {
            sprintf(printbuffer, "A known length %s", text1);
            list_states(rule_x, *position, trace_marks, p, printbuffer);
         }
         result = true;
         goto exit_point;
      }
      if (rhs_len[rule_x] == unspec_len && !multi_mark) {
         *position = mark_position;
         if (list_trace) {
            sprintf(printbuffer, "A %s", text);
            list_states(rule_x, *position, trace_marks, p, printbuffer);
         }
         result = true;
         goto exit_point;
      }
      /*  UNKNOWN LENGTH, MULTIPLE MARKS IF HERE  */;
      *position = mark_position;
      if (list_trace) {
            sprintf(printbuffer, "The leftmost of the %ss", text);
            list_states(rule_x, *position, trace_marks, p, printbuffer);
      }
      result = true;
   exit_point:
      freestring(&text);
      freestring(&text1);
      freebits(&trace_marks[0]);
      freebits(&trace_marks[1]);
      return result;
   }

   void find_left_part(start_set, reduce_follow, rule_x, length, best_lhs)

   set_of_states start_set;
   set_of_syms reduce_follow;
   rule_no rule_x;
   int length;
   vocab_symbol *best_lhs;
   {
      /* LOOK AT ALL LHS'S AND FIND THE "BEST".
         1) THE PRESENCE VECTOR SHOULD MATCH THE STATES TRACED BACK TO (THAT
            IS, THERE SHOULD BE A GOTO FOR EACH POSITION THAT COULD GENERATE
            THIS L.H.S.)
         2) THE REDUCE SPECIFIES A FOLLOW SET.  THE GOTOS ABOVE SHOULD KNOW
/* #### Page 6 *//*
            WHAT TO DO WITH ANYTHING IN THAT FOLLOW SET. IF NO PERFECT MATCH
            IS FOUND, A PARTIAL MATCH IS FOUND AND USED.
         When used in unslr:
         3) A FLAG SET TO INDICATE STATE SPLITTING NEEDED LATER TO REFINE
            THE TABLE AND THE RESULTING GRAMMAR.
      */

      boolean exact_match;
      vocab_symbol nt_sym;
      int gtf_size, goto_size;
      set_of_syms best_gtf = NULLBITS;
      set_of_states best_goto = NULLBITS;
      int best_gtf_size, best_goto_size;
      set_of_syms lim_goto_follow = NULLBITS;

      set_of_states t_s = NULLBITS;

      *best_lhs = 0;
      exact_match = false;
      /*  COMPUTE THE PRESENCE VECTOR FROM THE LAST COLUMN OF THE TRACE BACK
      TABLE  */
      for (nt_sym = first_nt; nt_sym <= last_nt; nt_sym++) {
         if (x_empty(plh[rule_x]) || x_test(plh[rule_x], nt_sym)) {
            /*  IS THIS GOING TO BE A SELF ( <U> ::= <U> ) RULE; IF SO IGNORE*/
            if (length == 1 && nt_sym == symbol_list[1]) continue;

            compute_lgtf(start_set, nt_sym, &lim_goto_follow);

            /* is it possible on both start set and reduce follow criteria? */
            /* N.B.: XPL uses temp booleans (POSSIBLE_xx) to implement this */
            if (!x_empty_minus(start_set, goto_set[nt_sym]) ||
                !x_empty_minus(reduce_follow, lim_goto_follow)) continue;
            if (x_equal(start_set, goto_set[nt_sym])
               && x_equal(lim_goto_follow, reduce_follow)) {
               if (!exact_match)
                  /*  NONE YET  */
                  *best_lhs = nt_sym;
               else {
                  /*  THERE WAS ANOTHER  */
                  sprintf(printbuffer,
                    " the left hand side for %d could be %s or %s",
                    rule_x, v[*best_lhs], v[nt_sym]);
                  error(printbuffer, 0);
               }
               exact_match = true;
               continue;
            }
/* #### Page 7 */
            if (exact_match) continue;

            gtf_size = x_count(lim_goto_follow);
            goto_size = x_count(goto_set[nt_sym]);
            if (*best_lhs == 0) {
               *best_lhs = nt_sym;
               best_gtf = newbits(lim_goto_follow);
               best_gtf_size = gtf_size;
               best_goto = newbits(goto_set[nt_sym]);
               best_goto_size = goto_size;
            }
            else if (gtf_size < best_gtf_size
               || (gtf_size == best_gtf_size && goto_size < best_goto_size)) {
               *best_lhs = nt_sym;
               freebits(&best_gtf);
               best_gtf = newbits(lim_goto_follow);
               best_gtf_size = gtf_size;
               freebits(&best_goto);
               best_goto = newbits(goto_set[nt_sym]);
               best_goto_size = goto_size;
            }
         }
      }

      freebits(&best_gtf);
      /* freebits(*best_goto); NOT THIS ONE... it's from a global */
      freebits(&lim_goto_follow);

      if (exact_match) {
         if (list_trace) printf("    %-10s   exact l.h.s\n", v[*best_lhs]);
         if (list_trace) single_space;
         return;
      }

      if (*best_lhs == 0) {
         sprintf(printbuffer, "no lhs found for rule %d", rule_x);
         error(printbuffer, 1);
         *best_lhs = last_nt + 1;
         return;
      }
      if (list_trace) printf("    %-10s   inexact l.h.s.\n", v[*best_lhs]);
      if (list_trace) single_space;
#ifdef UNSLR
      {
      split_index i;
      split_index empty_slot;

      subsets_found = true;
      /*  IS THIS THE NT WE ARE SPLITTING IN THIS ITERATION OF THE ALGORITHM.
          IF NOT WE ARE DONE WITH THIS RULE  */
      if (nt_to_split != 0 && nt_to_split != *best_lhs) return;

      nt_to_split = *best_lhs;
      empty_slot = - 1;
      /*  DOES THIS COVER OR IS IT COVERED BY ANOTHER RULES CONTEXTS  */
/* #### Page 8 */
      for (i = 0; i <= split_count; i++) {
         if (split_rule[i] != 0) {

            if (x_empty_minus(reduce_follow, split_rf[i])
             && x_empty_minus(start_set, split_ss[i])) {
               return; /*  COVERED, DON*T BOTHER  */
            }

            if (x_empty_minus (split_rf[i],reduce_follow)
             && x_empty_minus(split_ss[i], start_set)) {
            /*  COVERS THIS ONE, ZAP IT  */
               split_rule[i] = 0;
               empty_slot = i;
             }
         }
         else empty_slot = i;
      }
      /*  IF NO EMPTY SLOT, ADD ONE  */
      if (empty_slot == - 1) {
         split_count = split_count + 1;
         empty_slot = split_count;
         if (split_count > MAX_NO_SPLITS) error("split too complex", 3);
      }
      /*  FILL IN THE EMPTY SLOT  */;
      split_rule[empty_slot] = rule_x;
      split_rf[empty_slot] = newbits(reduce_follow);
      split_ss[empty_slot] = newbits(start_set);
      }
#endif /* UNSLR */
   }

   void find_rule(rule_no rule_x, set_of_syms *rf, set_of_states *start_set)
   {
      /*  TRACES THE STATES TO ARRIVE AT A RX ENTRY  */
      set_of_states p[21];
      int position;
      int i;
      table_state state;
      vocab_symbol lhs;
      boolean success;
      bitstring trace_marks[2];
      for (i=0; i<=20; i++) {
         p[i] = NULLBITS;
      }
      trace_marks[0] = NULLBITS;
      trace_marks[1] = NULLBITS;
      success = find_reduces(rule_x, &p[0], rf);
      reduce_set[rule_x] = newbits(p[0]);
      if (success) {
         find_right_part(rule_x, p, *rf, trace_marks, &position);
/* #### Page 9 */
         *start_set = newbits(p[position]);
         p[position] = NULLBITS;
         find_left_part(*start_set, *rf, rule_x, position, &lhs);
         /*  RECORD THE TEXT OF THE RULE  */
         inc_prod_array_ptr();
         prod_array[prod_array_ptr] = lhs;
         x_setempty(&plh[rule_x]);
         x_set(&plh[rule_x], lhs);
         prod_start[rule_x] = prod_array_ptr;
         rhs_len[rule_x] = position;
         for (i = 1; i <= position; i++) {
            inc_prod_array_ptr();
            prod_array[prod_array_ptr] = symbol_list[position - i + 1];
         }
         for (state = 0; state <= no_states; state++) {
            if (x_test(p[position], state)) x_set(&in_start_set[state], rule_x);
         }
      }
      else {
         sprintf(printbuffer, "reduction %d does not appear in table.", rule_x);
         error(printbuffer, 0);
         prod_start[rule_x] = 0;        /*  A ZERO MEANS NO RULE  */
         x_setempty(&plh[rule_x]);
         rhs_len[rule_x] = 0;
      }
      for (i=1; i<20; i++) { /*  not p[O]; it got saved */
         freebits(&p[i]);
      }
      freebits(&trace_marks[0]);
      freebits(&trace_marks[1]);
   }
void extract_grammar()
{
   vocab_symbol nt_sym;
   rule_no redn;
#ifdef UNSLR
   /*  INITIALIZE THE SPLITTING TABLES  */;
   nt_to_split = 0;
   split_count = - 1;
#endif
   prod_array_ptr = 1; /*  RESET IT FOR EACH TIME  */
   for (nt_sym = first_nt; nt_sym <= last_nt; nt_sym++) {
      compute_goto_set(nt_sym);
   }
   for (redn = 1; redn <= no_prods; redn++) {
      find_rule(redn, &reduce_follow[redn], &start_set[redn]);
   }
}
