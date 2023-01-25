package com.kreog.antlr.java;

import java.util.ArrayList;
import java.util.List;

public class AlgebraGrammarASTCall extends AlgebraGrammarASTExpr {
    public AlgebraGrammarASTExpr name;
    public List<AlgebraGrammarASTExpr> params = new ArrayList<>();
}
