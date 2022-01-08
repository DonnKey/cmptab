/* #### Page 1 */
#define ls 0    /*  LISTING OF INPUT TABLE  */
#define lf 1    /*  LISTING OF FORMATTED TABLE  */
#define lt 2    /*  LISTING OF TRACE OF PRODS  */
#define ig 3    /*  LISTING OF INTERMEDIATE GRAMMARS  */
#define it 4    /*  LISTING OF INTERMEDIATE TABLES  */
#define ft 5    /*  LISTING OF FINAL TABLE  */
#define fg 6    /*  LISTING OF FINAL GRAMMAR  */
#define sd 7    /*  PRINT SPLITTING DECISIONS  */
#define pg 8    /*  PUNCH THE RESULTING GRAMMARS  */
#define pi 9    /*  PUNCH THE INTERMEDIATE TABLES  */
#define ea 10   /*  EJECT AFTER ALL OUTPUT  */
#define pf 11   /*  PUNCH FINAL GRAMMAR  */
#define il 12   /*  INPUT LENGTH OF RULES  */
#define ap 13   /*  LIST TABLE AFTER PHI-INACC. TEST BUT BEFORE SPLIT  */
#define go 14   /*  RECOVER GRAMMAR ONLY, NO FIX UP  */
#define ie 15   /*  IGNORE ERRORS ON INPUT  */
#define pt 16   /*  PUNCH FINAL TABLES  */
#define sl 17   /*  SLR1 PRESERVING COMPRESSIONS ONLY   */
#define dl 18   /*  **DEBUG**  */
#define d2 d1+1 /*  **DEBUG**  */
#define d3 d1+2 /*  **DEBUG**  */
#define d4 d1+3 /*  **DEBUG**  */
#define d5 d1+4 /*  **DEBUG**  */

extern boolean control[];
extern boolean list_trace;
