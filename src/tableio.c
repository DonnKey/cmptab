/* #### Page 1 */
#include <stdio.h>
#include <string.h>

#include "utility.h"
#include "type.h"
#include "bitstring.h"
#include "options.h"
#include "nextitem.h"
#include "symbol.h"
#include "grammar.h"
#include "table.h"
#include "tableio.h"

extern FILE *mso;

char *format_action(pair)
table_entry pair;
{
   /*  CREATE A PRINTABLE VERSION OF THE TABLE ENTRY  */
   static char *text[5] = {"-", "s", "r", "a", "e"};
   action i;
   static char str[20];
   char s;

   if ((pair & 0x8000) != 0) s = '*';
   else s = ' ';

   i = action_type(pair);
   if (i == SHIFT || i == REDUCE) {
        sprintf(str,"%c%s%d",s,text[i],action_state(pair));
   }
   else {
        sprintf(str,"%c%s",s,text[i]);
   }
   return str;
}

void read_table()
{
   /*  INPUT THE TABLE  */
   char *result_item, *statename;
   rule_no rule;
   table_state state_no;
   vocab_symbol sym;
   table_state state;   /*  THE CURRENT STATE NAME  */
   boolean ambiguous_state;
   int a;       /*  SCRATCH  */
/* #### Page 2 */
   x_setempty(&states_used);
   /*  READ THE NUMBER OF STATES  */;
   next_item(&result_item);
   no_states = integer(result_item, "number of states");

   /*  READ THE NUMBER OF RULES AND SET LEN TO UNSPECIFIED  */
   next_item(&result_item);
   no_prods = integer(result_item, "number of reductions");

   next_item(&result_item);     /*  CLEAR THE CARD  */

   /*  READ THE VOCABULARY  */;
   sym = 1;
   while (next_item(&result_item)) {
      v[sym] = newstring(result_item);
      sym = sym + 1;
   }
   no_terminals = sym - 1;
   while (next_item(&result_item)) {
      v[sym] = newstring(result_item);
      sym = sym + 1;
   }
   no_nts = sym - no_terminals - 1;
   largest_nt = last_nt + 10;

   /*  READ THE TABLE BODY, ALL TERMINALS  */
   for (state_no = 0; state_no <= no_states; state_no++) {

      next_item(&result_item);
      if (e_o_f) {
         error("insufficient input", 2);
         return;
      }

      state = integer(result_item, "state #");
      if (x_test(states_used, state))
         error("state previously defined", 1);
      else
         x_set(&states_used, state);

      for (sym = 1; sym <= no_terminals; sym++) {
         next_item(&result_item);
         if (e_o_f) {
            error("insufficient input", 2);
            return;
         }

         statename = result_item;  /* keep it around for later errors */

         if (result_item[0] == '*') {
            result_item++;
            ambiguous_state = true;
         }
         else
            ambiguous_state = false;
/* #### Page 3 */

         switch(result_item[0]) {

         case 's':      /*  SHIFT  */
            a = integer(&result_item[1], "shift rule");
            action_table(state, sym) = action_pair(ambiguous_state, SHIFT, a);
            if (accessing_symbol[a] == 0)
               accessing_symbol[a] = sym;
            else if (accessing_symbol[a] != sym) {
               sprintf(printbuffer, "state %d has accessing symbols %s and %s",
                  a, v[sym], v[accessing_symbol[a]]);
               error(printbuffer, 1);
            }
            break;

         case 'r': /*  REDUCE  */
            a = integer(&result_item[1], "reduce rule");
            action_table(state, sym) = action_pair(ambiguous_state, REDUCE, a);
            break;

         case 'e': /*  ESSENTIAL ERROR  */
            action_table(state, sym)
               = action_pair(ambiguous_state, ESSENTIAL_ERROR, 0);
            break;

         case '-':
            action_table(state, sym) = action_pair(ambiguous_state, PHI, 0);
            break;

         case 'a':
            action_table(state, sym) = action_pair(false, ACCEPT_STATE, 0);
            break;

         default:
            sprintf(printbuffer, "undefined input %s", statename);
            error(printbuffer, 1);
            action_table(state, sym) = phi_entry;
         }
      }

      sym = first_nt;
      /*  READ ONLY AS MANY NT-S AS PROVIDED  */

      while (next_item(&result_item)) {
         if (sym <= last_nt) {

            switch(result_item[0]) {

            case 'e':
            case '-':
                action_table(state, sym) = phi_entry;
                break;

            case 's': /*  GOTO (=SHIFT)  */
                a = integer(&result_item[1], "shift goto rule");
                goto insert;
/* #### Page 4 */

            default:
                a = integer(result_item, "normal goto rule");
            insert:
                action_table(state, sym) = action_pair(false, GOTO, a);
                if (accessing_symbol[a] == 0) accessing_symbol[a] = sym;
                else if (accessing_symbol[a] != sym) {
                   sprintf(printbuffer,
                      "state %d has accessing symbols %s and %s",
                      a, v[sym], v[accessing_symbol[a]]);
                   error(printbuffer, 1);
                }
                break;
            }
            sym = sym + 1;
         }
      }
   }

   /*  READ RULE LENGTHS IF PROVIDED  */
   if (control[il]) {
      for (rule = 1; rule <= no_prods; rule++) {

         /* ignore end of card */
         if (!next_item(&result_item)) next_item(&result_item);
         if (e_o_f) {
            sprintf(printbuffer, " length/lhs not found for rule %d", rule);
            error(printbuffer, 1);
            break;
         }

         sprintf(printbuffer, "rule length %d", rule);
         rhs_len[rule] = integer(result_item, printbuffer);

         /* ignore end of card */
         if (!next_item(&result_item)) next_item(&result_item);
         for (sym = first_nt; sym <= last_nt; sym++) {
            if (strcmp(result_item, v[sym]) == 0) {
               x_setempty(&plh[rule]);
               x_set(&plh[rule], sym);
               goto search_done;
            }
         }
         sprintf(printbuffer, " symbol %s not found as a lhs", result_item);
         error(printbuffer, 1);

         search_done:;
      }
   }
}

/*                   **********************************
                     *                                *
                     *          ECHO TABLE            *
                     *                                *
                     **********************************
*/
/* #### Page 5 */
void echo_table()
{
/*  PRINT A FORMATTED VERSION OF THE CURRENT TABLE  */
   vocab_symbol n;
   table_entry actn_entry;
   rule_no rule;
   table_state state;
   vocab_symbol symbol;

   static boolean first_time = true;

   if (!first_time) {
      eject_page;
   }
   else
      first_time = false;
   printf("                      t h e   v o c a b u l a r y\n\n");
   printf("     t e r m i n a l  s y m b o l s     n o n t e r m i n a l s\n\n");

   for (n = 1; n <= max(no_terminals, no_nts); n++) {
      /*  PRINT THE VOCABULARY  */
      printf("%3d  ",n);
      /*  TERMINAL SYMBOLS  */
      printf("%-35.34s",n<=no_terminals?v[n]:"");
      /*  NONTERMINAL SYMBOLS  */
      if (n <= no_nts) printf("%s", v[n + no_terminals]);
      printf("\n");
   }

   single_space;
   printf("Rule length and lhs\n");

   for (rule = 1; rule <= no_prods; rule++) {
      if (prod_start[rule] != 0 || rhs_len[rule] == unspec_len) {
         printf("%3d: ", rule);
         if (rhs_len[rule] == unspec_len)
            printf(" ?");
         else
            printf("%2d, ", rhs_len[rule]);
         printf("%-10.10s ", v[prod_array[prod_start[rule]]]);
         if (rule % 4 == 0) printf("\n");
      }
   }
   if (rule % 4 != 0) printf("\n");

   if (max(no_terminals, no_nts) > 20)
      eject_page;
   else
      double_space;

   printf("The shift/reduce table\n");
   printf("  state         symbols\n");
   printf("        ");

   /* print a header; odd numbers on the first line, even on the second */
/* #### Page 6 */
   for (symbol = 0; symbol < (no_terminals+1)/2 ; symbol++) {
      printf("    %4d",2*symbol+1);
   }
   if ((no_terminals % 2) == 0) printf("    ");
   printf(" |");

   for (symbol = 0; symbol < (no_nts+1)/2 ; symbol++) {
      printf("%4d    ",2*symbol+1);
   }
   printf("\n");

   /* evens */
   printf("            ");
   for (symbol = 1; symbol < (no_terminals+2)/2; symbol++) {
      printf("    %4d", 2*symbol);
   }
   if ((no_terminals % 2) != 0) printf("    ");
   printf(" |    ");

   for (symbol = 1; symbol < (no_nts+2)/2; symbol++) {
      printf("%4d    ",2*symbol);
   }
   printf("\n");

   /* now do the real work */
   for (state = 0; state <= no_states; state++) {
      printf(" %6.6s", v[accessing_symbol[state]]);
      printf("%3d |",state);
      for (symbol = 1; symbol <= no_terminals; symbol++) {
         actn_entry = full_action(state, symbol);
         printf("%4s",format_action(actn_entry));
      }
      printf(" |");
      for (symbol = first_nt; symbol <= last_nt; symbol++) {
         actn_entry = full_action(state, symbol);
         if (action_type(actn_entry) == GOTO)
                printf("%4d", action_state(actn_entry));
         else
                printf("    ");
      }
      printf("\n");
   }
   single_space;
}

void punch_table()
{
   /*  PUNCH IN MACHINE READABLE FORM  */
   rule_no n;
   char *str;
   table_entry actn_entry;
   table_state state;
   vocab_symbol symbol;
   int charpos;

   fprintf(mso,"%d %d\n", no_states, no_prods);
/* #### Page 7 */
   charpos = 0;
   for (symbol = 1; symbol <= no_terminals; symbol++) {
      fprintf(mso,"%s ",v[symbol]);
      if ((charpos += strlen(v[symbol])+1) > 65) {fprintf(mso,"$\n");charpos=0;}
   }
   fprintf(mso,"\n");

   charpos = 0;
   fprintf(mso,"   ");
   for (symbol = first_nt; symbol <= last_nt; symbol++) {
      fprintf(mso,"%s ", v[symbol]);
      if ((charpos += strlen(v[symbol])+1) > 65) {fprintf(mso,"$\n");charpos=0;}
   }
   fprintf(mso,"\n");

   charpos = 0;
   for (state = 0; state <= no_states; state++) {
      fprintf(mso, "%3d", state);
      for (symbol = 1; symbol <= last_nt; symbol++) {
         actn_entry = full_action(state, symbol);
         fprintf(mso,"%4s ",format_action(actn_entry));
         if ((charpos += strlen(v[symbol])+1) > 75) {fprintf(mso,"$\n");charpos=0;}
      }
      fprintf(mso,"\n");
      charpos = 0;
   }

   charpos = 0;
   for (n = 1; n <= no_prods; n++) {
      if (prod_start[n] == 0)
         str = "?";
      else
         str = v[prod_array[prod_start[n]]];
      if (str == NULL) {
         str = "??";
      }

      fprintf(mso, "%2d %-12s ", rhs_len[n], str);
      if ((charpos += min(strlen(str),14)+4) > 75) {fprintf(mso,"$\n");charpos=0;}
   }
   fprintf(mso,"\n");
}
