/* #### Page 1 */
#include <stdio.h>
#include <string.h>

#include "type.h"
#include "options.h"
#include "utility.h"
#include "nextitem.h"

/*                      ******************************
                        *                            *
                        *         READ INPUT         *
                        *                            *
                        ******************************
*/

#define CARD_SIZE 200
boolean e_o_f = false;  /*  GLOBAL FOR TESTING  */
static int card_ptr = 999, card_len;
static char card_image[CARD_SIZE];
static boolean continued_card;

/* static */ boolean read_card()
{
      int j;

      if (e_o_f) return false;
      /*  READ AND RETURN A CARD IMAGE OR FALSE ON EOF  */;
      card_ptr = 0;
      while (true) {
         if (fgets(card_image, CARD_SIZE-1, stdin) == NULL) {
            e_o_f = true;
            return false;
         }
         /*  GUARANTEE A BLANK IN TEST FOR META BRACKETS. */
         if (control[ls]) printf("%s", card_image);
         card_len = strlen(card_image);
         card_len--;
         card_image[card_len] = ' ';
         continued_card = (card_image[card_len-1] == '$');
         if (continued_card) { card_len--; card_image[card_len] = ' '; }
         for (j=0; j<card_len; j++) if (card_image[j] != ' ') return true;
      }
}

/*  GET THE NEXT_TOKEN OFF THE CARD.  RETRUN TRUE IF MORE CARD REMAINS,
    FALSE IF AT END OF THE CARD (OR EOF). TOKENS ARE EITHER CONVENTIONAL BLANK
    SEPARATED STRINGS OR STRINGS (CONTAINING BLANKS) ENCOLSED IN META BRACKETS*/

boolean next_item(result1)
char **result1;
{
   int i, j;
   char str[100];
   char *symbol;
   int lp;
   char stop;   /*  THE RIGHT DELIMITER.  */
/* #### Page 2 */
   boolean no_stop_found;

   if (card_ptr >= 999 && !read_card()) return false;
   while (true) {
      /*  WATCH FOR ABNORMAL EXITS FROM THIS LOOP  */
      if (card_ptr >= card_len) {
              if (continued_card) {
                 if (!read_card()) return false;
              }
              else break;
      }

      if (card_image[card_ptr] != blank) {
         lp = card_ptr;         /*  MARK LEFT BOUNDARY  */
         if (card_image[lp] == left_bracket && card_image[lp + 1] != blank)
               stop = right_bracket;
         else  stop = blank;
         /*  NOW LOOK FOR STOP  */;
         no_stop_found = true;
         while (no_stop_found && card_ptr < card_len) {
            card_ptr = card_ptr + 1;
            if (card_image[card_ptr] == stop) no_stop_found = false;
         }
         /*  IN CASE MATCHING RIGHT BRACKET IS NOT FOUND  */
         if (no_stop_found && stop != blank) {
            sprintf(str,"unmatched bracket: %c starting at %s",
               stop, card_image[lp]);
            error(str,0);
            stop = blank;
            card_ptr = lp;
            /*  ERROR RECOVERY  */
            while (card_image[card_ptr] != blank && card_ptr < card_len) {
               card_ptr = card_ptr + 1;
            }
         }
         if (stop != blank && card_ptr < card_len) card_ptr++;
         if (card_image[card_ptr] != blank && card_image[card_ptr] != '\0') {
            sprintf(str,"space must follow bracket: starting at %s",
                card_image[lp]);
            error(str,0);
         }
         /*  PICK UP LAST CHARACTER  */
         /*  IT WAS A SYMBOL, LOOK UP AND RETURN  */
         *result1 = &card_image[lp];
         card_image[card_ptr] = '\0';
         card_ptr++;
         return true;
      }
      card_ptr = card_ptr + 1;
   }
   card_ptr = 999;
   return false;        /*  WHEN AT END OF CARD  */
}
