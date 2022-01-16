# cmptab
SLR1 table compression with (ambiguous) grammar extraction

This program is one of a pair to compress and expand SLR(1) (and some LR(1)) 
grammars along with their corresponding tables.

For much more documentation, see unslr, the table expansion program, adjacent to this repository
in GitHub. The README for that program has more extensive comments and much
more on testing.

To summarize:

The tables can be considered something like a "Fourrier Transform" of the 
grammar -- another way to look at the same information, and thus manipulate 
that information more easily for certain tasks.

This interacts strongly with ambiguous grammars: the compressed tables 
correspond to ambiguous grammars for which ambiguity resolution information has 
been applied to the table.

Table expansion of tables with ambiguity resolution recovers an unambiguous 
grammar for that particular ambiguity resolution. The grammars so recovered are 
often ones that would take a great deal of thought to arrive at in terms of 
manipulating the grammar: as an example it finds a nice grammar for the C ?: 
operator such that only expressions which would be "ambiguous" to the casual 
reader of such a statement are required to be parenthesised.

The algoritghms used are discussed in detail in:

||
| ------------ |
| Ambiguity and LR Parsing |
| Donn Scott Terry |
Department of Computer Science (now Allen School of Computer Science)
Technical Report No. 78-11-02
University of Washington