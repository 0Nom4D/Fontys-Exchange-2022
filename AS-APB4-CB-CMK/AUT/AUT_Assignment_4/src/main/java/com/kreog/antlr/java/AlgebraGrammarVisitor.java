package com.kreog.antlr.java;

import com.kreog.antlr.AlgebraGrammarBaseVisitor;
import com.kreog.antlr.AlgebraGrammarParser;

import java.util.List;

public class AlgebraGrammarVisitor extends AlgebraGrammarBaseVisitor<AlgebraGrammarAST> {
    @Override
    public AlgebraGrammarAST visitParenExpr(AlgebraGrammarParser.ParenExprContext ctx) {
        return visit(ctx.expr());
    }

    @Override
    public AlgebraGrammarAST visitNumExpr(AlgebraGrammarParser.NumExprContext ctx) {
        AlgebraGrammarASTNumber value = new AlgebraGrammarASTNumber();

        value.number = Float.valueOf(ctx.NUMBER().getText());
        return value;
    }

    @Override
    public AlgebraGrammarAST visitStatementIf(AlgebraGrammarParser.StatementIfContext ctx) {
        AlgebraGrammarASTIf ifExpression = new AlgebraGrammarASTIf();

        AlgebraGrammarASTExpr boolExpr = (AlgebraGrammarASTExpr) visit(ctx.expr());
        AlgebraGrammarASTExpressions left = (AlgebraGrammarASTExpressions) visit(ctx.left);
        AlgebraGrammarASTExpressions right = (AlgebraGrammarASTExpressions) visit(ctx.right);
        ifExpression.cond = boolExpr;
        ifExpression.left = left;
        ifExpression.right = right;
        return ifExpression;
    }

    @Override
    public AlgebraGrammarAST visitStatementWhile(AlgebraGrammarParser.StatementWhileContext ctx) {
        AlgebraGrammarASTWhile whileExpression = new AlgebraGrammarASTWhile();

        AlgebraGrammarASTExpr expr = (AlgebraGrammarASTExpr) visit(ctx.expr());
        AlgebraGrammarASTExpressions statements = (AlgebraGrammarASTExpressions) visit(ctx.expressions());
        whileExpression.cond = expr;
        whileExpression.exprs = statements;
        return whileExpression;
    }

    @Override
    public AlgebraGrammarAST visitFunctionExpr(AlgebraGrammarParser.FunctionExprContext ctx) {
        AlgebraGrammarASTFunction function = new AlgebraGrammarASTFunction();
        AlgebraGrammarParser.ParametersContext params = ctx.parameters();
        for (AlgebraGrammarParser.AtomContext i : params.atom()) {
            AlgebraGrammarASTAtom atom = new AlgebraGrammarASTAtom();
            atom.name = i.getText();
            function.parameters.add(atom);
        }
        function.statements = (AlgebraGrammarASTExpressions) visit(ctx.expressions());
        return function;
    }

    @Override
    public AlgebraGrammarAST visitCallExpr(AlgebraGrammarParser.CallExprContext ctx) {
        AlgebraGrammarASTCall call = new AlgebraGrammarASTCall();
        call.name = (AlgebraGrammarASTExpr) visit(ctx.primary());
        AlgebraGrammarParser.CallparametersContext params = ctx.callparameters();
        for (AlgebraGrammarParser.ExprContext i : params.expr()) {
            call.params.add((AlgebraGrammarASTExpr) visit(i));
        }
        return call;
    }

    @Override
    public AlgebraGrammarAST visitExpressionExpr(AlgebraGrammarParser.ExpressionExprContext ctx) {
        return visit(ctx.expr());
    }

    @Override
    public AlgebraGrammarAST visitExpressionStatement(AlgebraGrammarParser.ExpressionStatementContext ctx) {
        return visit(ctx.statement());
    }

    @Override
    public AlgebraGrammarAST visitExpressions(AlgebraGrammarParser.ExpressionsContext ctx) {
        List<AlgebraGrammarParser.ExpressionContext> exprs = ctx.expression();
        AlgebraGrammarASTExpressions exprList = new AlgebraGrammarASTExpressions();

        exprList.statementList.clear();
        for (AlgebraGrammarParser.ExpressionContext i : exprs) {
            var result = visit(i);
//            if (!(result instanceof AlgebraGrammarASTStatement || result instanceof AlgebraGrammarASTExpr)) {
//                throw new IllegalArgumentException("One or more statement aren't valid in the input file.");
//            }
            exprList.statementList.add(result);
        }
        return exprList;
    }

    @Override
    public AlgebraGrammarAST visitPrimaryExpr(AlgebraGrammarParser.PrimaryExprContext ctx) {
        return visit(ctx.primary());
    }

    @Override
    public AlgebraGrammarAST visitStatementAssign(AlgebraGrammarParser.StatementAssignContext ctx) {
        AlgebraGrammarASTAssign varAssign = new AlgebraGrammarASTAssign();
        AlgebraGrammarASTAtom atom = new AlgebraGrammarASTAtom();

        atom.name = ctx.atom().getText();
        varAssign.value = atom;

        var result = visit(ctx.expr());
//        if (!(result instanceof AlgebraGrammarASTExpr)) {
//            throw new IllegalArgumentException("Atom must be assign to an expression.");
//        }
        varAssign.expr = (AlgebraGrammarASTExpr) result;
        return varAssign;
    }

    @Override
    public AlgebraGrammarAST visitStatementPrint(AlgebraGrammarParser.StatementPrintContext ctx) {
        var result = visit(ctx.expr());

//        if (!(result instanceof AlgebraGrammarASTExpr)) {
//            throw new IllegalArgumentException("Print statement must take an expression as parameter.");
//        }
        AlgebraGrammarASTPrint printStatement = new AlgebraGrammarASTPrint();

        printStatement.expr = (AlgebraGrammarASTExpr) result;
        return printStatement;
    }

    @Override
    public AlgebraGrammarAST visitStatementReturn(AlgebraGrammarParser.StatementReturnContext ctx) {
        var result = visit(ctx.expression());

        AlgebraGrammarASTReturn returnStatement = new AlgebraGrammarASTReturn();
        returnStatement.expr = result;
        return returnStatement;
    }

    @Override
    public AlgebraGrammarAST visitAtomMainExpr(AlgebraGrammarParser.AtomMainExprContext ctx) {
        AlgebraGrammarASTAtom atom = new AlgebraGrammarASTAtom();

        atom.name = ctx.getText();
        return atom;
    }

    @Override
    public AlgebraGrammarAST visitOpExpr(AlgebraGrammarParser.OpExprContext ctx) {
        var left = visit(ctx.left);
        var right = visit(ctx.right);

//        if (!(left instanceof AlgebraGrammarASTExpr && right instanceof AlgebraGrammarASTExpr)) {
//            throw new IllegalArgumentException("Operation must have a left and a right valid expression.");
//        }
        String op = ctx.op.getText();

        AlgebraGrammarASTExpr expr = new AlgebraGrammarASTExpr();
        expr.left = (AlgebraGrammarASTExpr) left;
        expr.operationOp = op;
        expr.right = (AlgebraGrammarASTExpr) right;
        return expr;
    }
}
