/* #### Page 1 */
#include <string.h>
#include <stdlib.h>

#include "type.h"
#include "options.h"
#include "utility.h"

char *options[] = {"ls", "lf", "lt", "ig", "it", "ft", "fg", "sd", "pg", "pi", "ea", "pf", "il", "ap", "go", "ie", "pt", "sl", "d1", "d2", "d3", "d4", "d5"};

boolean control[sizeof(options)/sizeof(char *)];

int error_count;
char *blank_card = "                                                                                ";

char printbuffer[200];  /*  for sprintf calls */

/*
                     ***************************************
                     *                                     *
                     *         utility  procedures         *
                     *                                     *
                     ***************************************
*/

void error(message, severity)
/*  print error message, increment error count.  */
char *message;
int severity;
{
   printf(" *** error, %s\n", message);
   switch (severity) {
   case 0: /* no-op */;
      break;
   case 1: error_count = error_count  + 1;
      break;
   case 2: exit(1);
      break;
   }
}

 /* ***************

 char* i_format(i, len, blank_zero)
/*  print in i format, blank when zero on switch  *?
int i, len;
boolean blank_zero;
{
static char str[80];

   if (blank_zero && i == 0) {
        strncpy(str, blank_card,80);
        str[len] = '\0';
   }
   else {
        sprintf(str,"%*d",len,i);
/* #### Page 2 *?
   }

   return str;
}

***** */

int max(i, j)
/* return max of i and j  */
int i, j;
{
   if (i > j) return i;
   return j;
}


int min(i, j)
/*  return min of i and j  */
int i, j;
{
   if (i < j) return i;
   return j;
}

/* ****************
#include <varargs.h>
#define MAXARGS    100
/* VARARGSO *?
char *concat(va_alist)
va_dcl
{
    va_list argp;
    int argno = O;
    static char str[500];
    char *t;

    str[O] ='\0';
    va_start(argp);
    while ((t = va_arg(argp, char *)) != (char *)0))
        strncat(str,t,500);
    va_end(argp);
    return str;
}
 ************************ */
int integer(str, msg)
/*  convert string to number and gripe if bad  */
char *str, *msg;
{
   long i;
   char *resptr;

   i = strtol(str, &resptr, 0);
   if (resptr == str || resptr != str + strlen(str)) {
      sprintf(printbuffer, "numeric error for %s reading %s, value %d was used.",
        msg, str, i);
/* #### Page 3 */
      error(printbuffer, 1);
   }
   return i;
}

 /* ******************

char *pad_l(in, string)
/*  pad to the left to len  *?
int ln;
char *string;
{
   static char str[80];

#ifdef checking
   if (ln > 80) error("strlen too long for pad_l; bye",2);
#endif
   if (strlen(str) >= ln) {
        strncpy(str, string, 80);
        str[lnj='\0';
   }
   else {
      strncpy(str, blank_card, ln-strlen(str)));
      strncat(str, string, 80);
   }
   return str;
}

char *pad_r(ln, string)
/*  pad to the right to len   *?
int ln;
char *string;
{
   static char str[80];
   strncpy(str, string, 80),
   if (strlen(str) >= ln) str[ln]='\O';
   else strncat(str, blank_card, ln);

   return str;
}

************* */

 /* ************
 void line_out(number, line)
/*  number a line and print it  *?
int number;
char *line;
{
   printf("%6d   %s",number,line);
}

******* */

void set_control(argc, argv)
/* #### Page 4 */
/*  scan card for options and set or reset control. */
char **argv;
int argc;
{
      int i, j;

   for (i=1; i<argc; i++) {
      for (j=0; j<(sizeof(options)/sizeof(char *)); j++) {
         if (strcmp(argv[i], options[j])==0) control[j] = true;
      }
   }
   if (control[lt]) control[sd] = true;
}
/* ***************
void condout(control_val, text)

int control_val;
char *text;
{
   if (control[control_val]) puts(text);
}
*********** */
char *newstring(s)
char *s;
{
        char *t;
        t=(char *)malloc (strlen(s)+1);
        strcpy(t,s);
        return t;
}

void freestring(s)
char **s;
{
        if (*s != NULL) free(*s);
        *s = NULL;
}
