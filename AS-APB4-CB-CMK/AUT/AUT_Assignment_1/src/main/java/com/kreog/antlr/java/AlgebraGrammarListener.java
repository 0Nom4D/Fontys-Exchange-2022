package com.kreog.antlr.java;

import com.kreog.antlr.AlgebraGrammarBaseListener;
import com.kreog.antlr.AlgebraGrammarParser;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.TerminalNode;

import java.util.Stack;

public class AlgebraGrammarListener extends AlgebraGrammarBaseListener {
    public final Stack<Double> argStack = new Stack<>();
    public final Stack<Integer> opStack = new Stack<>();

    public double getResult() {
        return this.argStack.pop();
    }

    @Override
    public void exitExpression(final AlgebraGrammarParser.ExpressionContext ctx) {
        handleExpression(ctx);
    }

    @Override
    public void exitExpr(final AlgebraGrammarParser.ExprContext ctx) {
        handleExpression(ctx);
    }

    private void handleExpression(final ParserRuleContext ctx) {
        if (ctx.getChildCount() == 3) {
            final double right = this.argStack.pop();
            final double left = this.argStack.pop();
            final int op = this.opStack.pop();
            switch (op) {
                case AlgebraGrammarParser.MUL -> this.argStack.push(left * right);
                case AlgebraGrammarParser.DIV -> this.argStack.push(left / right);
                case AlgebraGrammarParser.PLUS -> this.argStack.push(left + right);
                case AlgebraGrammarParser.MINUS -> this.argStack.push(left - right);
            }
        }
    }

    @Override
    public void visitTerminal(final TerminalNode node) {
        final Token symbol = node.getSymbol();
        final int type = symbol.getType();
        switch (type) {
            case AlgebraGrammarParser.NUMBER -> this.argStack.push(Double.valueOf(symbol.getText()));
            case AlgebraGrammarParser.MINUS, AlgebraGrammarParser.PLUS, AlgebraGrammarParser.DIV, AlgebraGrammarParser.MUL ->
                    this.opStack.add(type);
            default -> {
            }
        }
    }
}
