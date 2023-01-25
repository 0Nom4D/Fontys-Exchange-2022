package com.kreog.antlr.java;

import java.util.ArrayList;
import java.util.List;

public class AlgebraGrammarASTFunction extends AlgebraGrammarASTExpr {
    public List<AlgebraGrammarASTAtom> parameters = new ArrayList<>();
    public AlgebraGrammarASTExpressions statements;
}
