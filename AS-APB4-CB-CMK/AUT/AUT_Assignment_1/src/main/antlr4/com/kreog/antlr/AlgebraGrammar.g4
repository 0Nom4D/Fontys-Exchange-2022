grammar AlgebraGrammar;

expression : expr;

expr
    : primary
    | expr (MUL | DIV) expr
    | expr (PLUS | MINUS) expr
    ;

primary
    : '(' expr ')'
    | NUMBER
    ;

// Terminal Nodes

NUMBER : ('-'* DIGIT* POINT DIGIT+) | ('-'* DIGIT+);
OPEN_PARAN : '(';
POINT : '.';
CLOSE_PARAN : ')';
DIGIT : [0-9];
MINUS : '-';
PLUS : '+';
DIV : '/';
MUL : '*';

WS : [ \t\n\r]+ -> skip;