/* #### Page 1 */
#define MAX_NO_STATES 100
#define MAX_NO_TABLE_ENTRIES 3000

typedef short table_entry;
typedef short table_state;

typedef char action;    /*  ACTION TYPE, POSSIBLE VALUES FOLLOW   */
#define PHI 0
#define SHIFT 1
#define GOTO 1          /*  THE SAME AS SHIFT   */
#define REDUCE 2
#define ACCEPT_STATE 3
#define ESSENTIAL_ERROR 4

table_entry a_t[MAX_NO_TABLE_ENTRIES];  /*  THE ACTUAL  TABLE OF ACTIONS  */
table_state no_states;                  /*  THE NUMBER OF STATES DEFINED  */

vocab_symbol accessing_symbol[MAX_NO_STATES];
table_entry phi_entry;                  /*  A CONSTANT OF  PHI  */
table_entry error_entry;                /*  A CONSTATNT OF ESSENTIAL_ERROR   */

#define action_table(i,j) (a_t[i*(largest_nt+1)+j])
#define stripped_action_table(i,j) (action_table(i,j)&0x7fff)
#define full_action(i,j) action_table(i,j)
#define action_pair(ambig,type,state) ((table_entry)((ambig&1) <<15)|((type&0x7f)<<8)|(state&0xff))

#define action_type(pair) ((action)(pair>>8)&0x7f)
#define action_rule action_state        /*  IT DOES BOTH   */
#define action_state(pair) ((table_state)(pair&0x7f))

typedef bitstring set_of_states;        /*  A SET OF TABLE_STATES   */
typedef int rule_no;                    /*  A RULE NUMBER   */
typedef bitstring set_of_rules;         /*  A SET OF RULE_NOS   */
set_of_states states_used;
set_of_states reduce_set[MAX_NO_PRODS];         /*  STATES CONTIAINING RX   */
set_of_syms plh[MAX_NO_PRODS];

void find_action();
table_state find_action_in_col();
