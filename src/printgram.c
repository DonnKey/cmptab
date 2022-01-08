/* #### Page 1 */
#include <stdio.h>
#include <string.h>

#include "type.h"
#include "utility.h"
#include "bitstring.h"
#include "symbol.h"
#include "grammar.h"

extern FILE *mso;

/*
                        ********************************
                        *                              *
                        *            PRINT_G           *
                        *                              *
                        ********************************
*/
vocab_symbol last_lhs_printed, last_lhs_punched;

void print_prod(n)
production_ptr n;
{
   production_symbols_ptr s;
   vocab_symbol sym;
   production_symbols_ptr var;

   sym = prod_array[prod_start[n]];
   /*  set up the left part   */
   if (sym == last_lhs_printed) {
      printf("%4d %.*s    |  ",n, strlen(v[sym]),blank_card);
   }
   else {
      printf("\n");
      printf("%4d %s  ::=  ",n,v[sym]);
   }
   last_lhs_printed = sym;
   /*  add on the right part  */
   var = prod_start[n];
   for (s = var + 1; s <= var + rhs_len[n]; s++) {
/*   if (left_precedence[prod_array[s]] != 0)
         printf(" (p%d)",left_precedence[prod_array[s]]);  */
     printf(" %s", v[prod_array[s]]);
/*   if (right_precedence[prod_array[s]] != 0)
         printf(" (p%d)  ",right_precedence[prod_array[s]]); */
   }
   printf("\n");
}
void punch_prod(n)
production_ptr n;
{
   production_symbols_ptr s;
   vocab_symbol sym;
   production_symbols_ptr var;
   char *text;
/* #### Page 2 */
   sym = prod_array[prod_start[n]];
   /*  SET UP THE LEFT PART   */
   if (sym == last_lhs_punched) {
      fprintf(mso, "%.*s ", strlen(v[sym]),blank_card);
   }
   else {
      fprintf(mso, "%s ",v[sym]);
   }
   /*  ADD ON THE RIGHT PART   */
   var = prod_start[n];
   for (s = var + 1; s <= var + rhs_len[n]; s++) {
      fprintf(mso, " %s",v[prod_array[s]]);
   }
   fprintf(mso, "\n");
   last_lhs_punched = sym;
}


void print_g(print, punch)
int print, punch;
{
   int lhs;
   char order[MAX_NO_SYMS];
   int n, i;

   /*  PRINT THE PRODUCTIONS   */;
   double_space;
   last_lhs_printed = last_lhs_punched = 0;
   if (print) {
      printf("                     t h e   p r o d u c t i o n s\n");
      double_space;
      printf("   The goal symbol is %s.\n",v[goal_symbol]);
   }
   /*  THE PRODUCTION ADDED AUTOMATICALLY IS NOT PRINTED  */;
   v[last_nt + 1] = "?";
   for (i = first_nt; i <= last_nt + 1; i++) {
      order[i] = i;
   }
   order[first_nt] = goal_symbol;
   order[goal_symbol] = first_nt;
   for (i = first_nt; i <= last_nt + 1; i++) {
      lhs = order[i];
      for (n = 1; n <= no_prods; n++) {
         if (prod_start[n] != 0 && prod_array[prod_start[n]] == lhs) {
            /*  IF ITS THERE   */
            if (print) print_prod(n);
            if (punch) punch_prod(n);
         }
      }
   }
   double_space;
}
