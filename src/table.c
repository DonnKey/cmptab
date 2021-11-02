/* #### Page 1 */
#include "type.h"
#include "bitstring.h"
#include "symbol.h"
#include "grammar.h"
#include "table.h"

/* ***************
table_entry action_table(i, j, k)
{
/* IMPLEMENTS A PSEUDO 2 DIMENSIONAL ARRAY ACTION_TABLE.
   RETURNS ONLY THE SIGINFICANT PART,WITHOUT THE FLAG BIT.
   BECAUSE OF THE NATURE OF PROCEDURE CALL CODE GENERATION
   THE STATEMENT ACTION_TABLE(A,B) = ACTION_TABLE(C,D)
   DOES NOT WORK PROPERLY.  IN ALL CASES  WHERE THIS IS DONE
   THE INTERMEDIATE VARIABLE K IS  USED TO MAKE IT WORK PROPERLY. *?
   table_state i;
   vocab_symbol j;
   table_entry k = infinity;

   int x;

   x = i * (largest_nt + 1) + j;
   if (x > MAX_NO_TABLE_ENTRIES)
        error("action table overflow",  2);
   if (k == infinity) { /*  CALLED ON  RIGHT  *?
      return a_t[x] & Ox7fff;
   }
   else {
      a_t[x] = k;
      k = infinity;
   }
}

table_entry full_action(i, j)
{
/* IMPLEMENTS A PSEUDO 2 DIMENSIONAL  ARRAY ACTION TABLE.
   THIS VERSION IS READ ONLY, AND  RETURNS THE FLAG BIT AS WELL
   AS THE REST OF THE DATA *?
   table_state i;
   vocab_symbol j;
   int x;

   x = i * (largest_nt + 1) + j;
   if (x > MAX_NO_TABLE_ENTRIES)
        error("action table overflow"   2);
   return a_t[x];
}
************/



void find_action(actn_entry, i, j)
table_entry actn_entry;
/* #### Page 2 */
table_state *i;
vocab_symbol *j;
{
   /*  FIND THE NEXT POSITION CONTAINING  ACTION STARTING FROM I,J RETURNS TRUE
   IF FOUND, WITH POSITION AS (I,J)  */
   int k;
   for (k = *i * (largest_nt + 1) + *j;
        k <= no_states * (largest_nt  + 1) + largest_nt; k++) {
      if ((a_t[k] & 0x7fff) ==  actn_entry) {
         *i = k / (largest_nt +  1);
         *j = k % (largest_nt +  1);
         return;
      }
   }
   *i = - 1;
   return;
}


table_state find_action_in_col(actn_entry,  i, j)
table_entry actn_entry;
table_state *i;
vocab_symbol j;
{
/* SIMILAR TO ABOVE BUT ONLY  LOOKS IN COLUMN SPECIFIED BY J */

int k;

   k = *i * (largest_nt + 1) +  j;
   for (; k <= no_states * (largest_nt  + 1) + largest_nt; k += largest_nt + 1) {
      if ((a_t[k] & 0x7fff) ==  actn_entry) {
         *i = k / (largest_nt + 1);
         return *i;
      }
   }
   *i = - 1;
   return - 1;
}
