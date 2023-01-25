grammar AlgebraGrammar;

expressions : (expression ';' )+;

expression
    : statement         #expressionStatement
    | expr              #expressionExpr
    ;

statement
    : PRINT expr        #statementPrint
    | IF OPEN_PARAN expr CLOSE_PARAN OPEN_CURLY expressions CLOSE_CURLY #statementIf
    | WHILE OPEN_PARAN expr CLOSE_PARAN OPEN_CURLY expressions CLOSE_CURLY #statementWhile
    | atom ASSIGN expr  #statementAssign
    ;

expr
    : primary                                #primaryExpr
    | left=expr op=(MUL | DIV) right=expr    #opExpr
    | left=expr op=(PLUS | MINUS) right=expr #opExpr
    | left=expr op=(EQUAL | NEQUAL) right=expr #opExpr
    ;

primary
    : OPEN_PARAN expr CLOSE_PARAN #parenExpr
    | NUMBER       #numExpr
    | atom         #atomExpr
    ;

atom
    : ALPHA+       #atomMainExpr
    ;

// Terminal Nodes

NUMBER : ('-'* DIGIT* POINT DIGIT+) | ('-'* DIGIT+);
IF : 'if';
WHILE : 'while';
OPEN_CURLY : '{';
CLOSE_CURLY : '}';
EQUAL : '==';
NEQUAL : '!=';
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