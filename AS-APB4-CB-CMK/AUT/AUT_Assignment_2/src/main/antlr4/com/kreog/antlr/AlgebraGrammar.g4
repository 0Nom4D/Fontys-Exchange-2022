grammar AlgebraGrammar;

expressions : (expression ';' )+;

expression
    : statement         #expressionStatement
    | expr              #expressionExpr
    ;

statement
    : PRINT expr        #statementPrint
    | atom ASSIGN expr  #statementAssign
    ;

expr
    : primary                                #primaryExpr
    | left=expr op=(MUL | DIV) right=expr    #opExpr
    | left=expr op=(PLUS | MINUS) right=expr #opExpr
    ;

primary
    : '(' expr ')' #parenExpr
    | NUMBER       #numExpr
    | atom         #atomExpr
    ;

atom
    : ALPHA+       #atomMainExpr
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
ASSIGN : '=';
ALPHA : [a-zA-Z];
PRINT : 'print';

WS : [ \t\n\r]+ -> skip;