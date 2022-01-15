/* #### Page 1 */
#define _POSIX_C_SOURCE 1
#include <stdio.h>

#include "type.h"
#include "utility.h"
#include "bitstring.h"
#include "symbol.h"
#include "grammar.h"
#include "table.h"
#include "tabbinio.h"

/*               
                 **********************************
                 *                                *
                 *          TABLE I/O             *
                 *                                *
                 **********************************
*/

static FILE *mx1;
static firsttime = 1;
static char *tempfile;

void packword(w)
int w;
{
        fwrite((char *)&w, sizeof(w), 1, mx1);
}

void packbits(str0)
bitstring str0;
{
        int w;

        w = x_size(str0);
        fwrite((char *)&w, sizeof(w), 1, mx1);
        fwrite((char *)str0, w, 1, mx1);
}
/* **********************
 void packstr(string)
char *string;   /*  OR BITS)  *?
{
      int len;

      len = strlen(string);
      packword(len);
      if (len == 0) return;
      fwrite(string, len, 1, mx1);
}
************************ */

void backup()
{
   table_state state_no;
   vocab_symbol sym;
/* #### Page 2 */
   rule_no rule;
   production_symbols_ptr ptr;
   char temp_name[] = "/tmp/cmptabXXXXXX";

   if (firsttime) {
           /* mx1 = fopen(tempfile = tmpnam(NULL),"w+"); */
           mx1 = fdopen(mkstemp(temp_name),"w+");
           /* unlink(tmpfile);  */
           firsttime = 0;
   }
   rewind(mx1);
   packword(no_terminals);
   packword(no_nts);
   packword(no_states);
   packword(no_prods);
   packword(prod_array_ptr);
   for (state_no = 0; state_no <= no_states; state_no++) {
      packword(accessing_symbol[state_no]);
   }
   for (rule = 1; rule <= no_prods; rule++) {
      packbits(reduce_set[rule]);
      packword(rhs_len[rule]);
      packword(prod_start[rule]);
   }
   for (ptr = 1; ptr <=prod_array_ptr; ptr++) {
      packword(prod_array[ptr]);
   }
   for (state_no = 0; state_no <= no_states; state_no++) {
      for (sym = 1; sym <= last_nt; sym++) {
         packword(stripped_action_table(state_no, sym));
      }
   }
   fflush(mx1);
}

int getword()
{
     int word;
     fread((char *)&word, sizeof(word), 1, mx1);

     return word;
}
bitstring getbits()
{
   bitstring string;     /*  OR BITS)  */
   int k;

   k = getword();
   if (k == 0) {
      x_setempty(&string);
      return string;
   }
   string = (bitstring)malloc (k);
   fread(string, k, 1, mx1);
   return string;
}
/* #### Page 3 */
void restore()
{
   char array[4];
   int i, j, k;
   table_state state_no;
   vocab_symbol sym;
   rule_no rule;
   production_symbols_ptr ptr;

   rewind(mx1);
   no_terminals = getword();
   no_nts = getword();
   no_states = getword();
   no_prods = getword();
   prod_array_ptr = getword();
   for (state_no = 0; state_no <= no_states; state_no++) {
      accessing_symbol[state_no] = getword();
   }
   for (rule = 1; rule <= no_prods; rule++) {
      reduce_set[rule] = getbits();
      rhs_len[rule] = getword();
      prod_start[rule] = getword();
   }
   for (ptr = 1; ptr <= prod_array_ptr; ptr++) {
      prod_array[ptr] = getword();
   }
   for (state_no = 0; state_no <= no_states; state_no++) {
      for (sym = 1; sym <= last_nt;  sym++) {
         action_table(state_no, sym) = getword();
      }
   }
}
