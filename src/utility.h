void error();
int max();
int min();
int integer();
/*
char *i_format();
char *pad_1();
char *pad_r();
void line_out();
*/
void set_control();
char *newstring();
void freestring();

extern char *blank_card;
extern int error_count;
extern char printbuffer[];

#define eject_page printf("\f")
#define double_space printf("\n\n")
#define single_space printf("\n")
