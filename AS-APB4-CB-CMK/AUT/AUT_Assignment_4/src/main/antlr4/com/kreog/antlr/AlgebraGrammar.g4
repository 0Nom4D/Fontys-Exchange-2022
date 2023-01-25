grammar AlgebraGrammar;

expressions : (expression ';' )+;

expression
    : statement         #expressionStatement
    | expr              #expressionExpr
    ;

statement
    : PRINT expr        #statementPrint
    | RETURN expression       #statementReturn
    | IF OPEN_PARAN expr CLOSE_PARAN OPEN_CURLY left=expressions CLOSE_CURLY ELSE OPEN_CURLY right=expressions CLOSE_CURLY #statementIf
    | WHILE OPEN_PARAN expr CLOSE_PARAN OPEN_CURLY expressions CLOSE_CURLY #statementWhile
    | atom ASSIGN expr  #statementAssign
    ;

parameters : (atom (COMMA atom)*)?;

callparameters : (expr (COMMA expr)*)?;

expr
    : primary                                #primaryExpr
    | left=expr op=(MUL | DIV) right=expr    #opExpr
    | left=expr op=(PLUS | MINUS) right=expr #opExpr
    | left=expr op=(EQUAL | NEQUAL) right=expr #opExpr
    ;

primary
    : OPEN_PARAN parameters CLOSE_PARAN OPEN_CURLY expressions CLOSE_CURLY #functionExpr
    | OPEN_PARAN expr CLOSE_PARAN #parenExpr
    | primary OPEN_PARAN callparameters CLOSE_PARAN #callExpr
    | NUMBER       #numExpr
    | atom         #atomExpr
    ;

atom
    : ALPHA+       #atomMainExpr
    ;

// Terminal Nodes

RETURN : 'return';
NUMBER : ('-'* DIGIT* POINT DIGIT+) | ('-'* DIGIT+);
IF : 'if';
WHILE : 'while';
OPEN_CURLY : '{';
CLOSE_CURLY : '}';
COMMA : ',';
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
ELSE : 'else';

WS : [ \t\n\r]+ -> skip;