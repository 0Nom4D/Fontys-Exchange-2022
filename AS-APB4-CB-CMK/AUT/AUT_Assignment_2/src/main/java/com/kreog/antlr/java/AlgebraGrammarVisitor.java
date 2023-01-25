package com.kreog.antlr.java;

import com.kreog.antlr.AlgebraGrammarBaseVisitor;
import com.kreog.antlr.AlgebraGrammarParser;
import org.antlr.v4.runtime.misc.NotNull;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;

public class AlgebraGrammarVisitor extends AlgebraGrammarBaseVisitor<Float> {
    public final HashMap<String, Float> varContext = new HashMap<>();

    @Override
    public Float visitParenExpr(@NotNull AlgebraGrammarParser.ParenExprContext ctx) {
        return visit(ctx.expr());
    }

    @Override
    public Float visitNumExpr(@NotNull AlgebraGrammarParser.NumExprContext ctx) {
        return Float.valueOf(ctx.NUMBER().getText());
    }

    @Override
    public Float visitExpressionExpr(@NotNull AlgebraGrammarParser.ExpressionExprContext ctx) {
        return visit(ctx.expr());
    }

    @Override
    public Float visitExpressionStatement(@NotNull AlgebraGrammarParser.ExpressionStatementContext ctx) {
        return visit(ctx.statement());
    }

    @Override
    public Float visitExpressions(@NotNull AlgebraGrammarParser.ExpressionsContext ctx) {
        List<AlgebraGrammarParser.ExpressionContext> exprs = ctx.expression();
        float lastResult = 0;
        for (AlgebraGrammarParser.ExpressionContext i : exprs) {
            lastResult = visit(i);
        }
        return lastResult;
    }

    @Override
    public Float visitPrimaryExpr(@NotNull AlgebraGrammarParser.PrimaryExprContext ctx) {
        return visit(ctx.primary());
    }

    @Override
    public Float visitStatementAssign(@NotNull AlgebraGrammarParser.StatementAssignContext ctx) {
        String atom = ctx.atom().getText();
        Float value = visit(ctx.expr());
        varContext.put(atom, value);
        return value;
    }

    @Override
    public Float visitStatementPrint(@NotNull AlgebraGrammarParser.StatementPrintContext ctx) {
        float value = visit(ctx.expr());
        System.out.println(ctx.expr().getText() + " = " + value + ";");
        return value;
    }

    @Override
    public Float visitAtomMainExpr(@NotNull AlgebraGrammarParser.AtomMainExprContext ctx) {
        String atom = ctx.getText();
        if (!varContext.containsKey(atom)) {
            throw new IllegalArgumentException("Unknown variable \"" + atom + "\"!");
        }
        return varContext.get(atom);
    }

    @Override
    public Float visitOpExpr(@NotNull AlgebraGrammarParser.OpExprContext ctx) {
        float left = visit(ctx.left);
        float right = visit(ctx.right);
        String op = ctx.op.getText();

        return switch (op.charAt(0)) {
            case '*' -> left * right;
            case '/' -> left / right;
            case '+' -> left + right;
            case '-' -> left - right;
            default -> throw new IllegalArgumentException("Unknown operator " + op);
        };
    }
}
