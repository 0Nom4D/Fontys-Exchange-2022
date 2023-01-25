package com.kreog.antlr.java;

import java.util.HashMap;

public class AlgebraGrammarExecutor {
    public final HashMap<String, AlgebraGrammarValue> varContext = new HashMap<>();

    public Float execNumber(AlgebraGrammarASTNumber num) {
        return num.number;
    }

    public AlgebraGrammarValue execAtom(AlgebraGrammarASTAtom atom) {
        if (!varContext.containsKey(atom.name)) {
            throw new IllegalAccessError("Unknown var: " + atom.name);
        }
        return varContext.get(atom.name);
    }

    public AlgebraGrammarValue execExpr(AlgebraGrammarASTExpr expr) {
        if (expr instanceof AlgebraGrammarASTNumber) {
            AlgebraGrammarValueFloat val = new AlgebraGrammarValueFloat();
            val.value = execNumber((AlgebraGrammarASTNumber) expr);
            return val;
        }
        else if (expr instanceof AlgebraGrammarASTAtom) {
            return execAtom((AlgebraGrammarASTAtom) expr);
        }

        AlgebraGrammarValue left = execExpr(expr.left);
        AlgebraGrammarValue right = execExpr(expr.right);
        
        if ((right instanceof AlgebraGrammarValueBool) && (left instanceof AlgebraGrammarValueBool)) {
            // Handle boolean expression
            Boolean rightBool = ((AlgebraGrammarValueBool) right).value;
            Boolean leftBool = ((AlgebraGrammarValueBool) left).value;
            AlgebraGrammarValueBool res = new AlgebraGrammarValueBool();
            res.value = switch (expr.operationOp.charAt(0)) {
                case '=' -> leftBool == rightBool;
                case '!' -> leftBool != rightBool;
                default -> throw new IllegalArgumentException("Unknown operator \"" + expr.operationOp + "\" for Boolean expression");
            };
            return res;
        }
        else if ((right instanceof AlgebraGrammarValueFloat) && (left instanceof AlgebraGrammarValueFloat)) {
            // Handle arithmetic expression
            Float rightFloat = ((AlgebraGrammarValueFloat) right).value;
            Float leftFloat = ((AlgebraGrammarValueFloat) left).value;
            // That is a dirty hack, but for now it will do
            if (expr.operationOp.equals("==") || expr.operationOp.equals("!=")) {
                AlgebraGrammarValueBool res = new AlgebraGrammarValueBool();
                res.value = switch (expr.operationOp.charAt(0)) {
                    case '=' -> leftFloat.equals(rightFloat);
                    case '!' -> !leftFloat.equals(rightFloat);
                    default -> throw new IllegalArgumentException("Unknown operator \"" + expr.operationOp + "\" for Boolean expression");
                };
                return res;
            }
            AlgebraGrammarValueFloat res = new AlgebraGrammarValueFloat();
            res.value = switch (expr.operationOp.charAt(0)) {
                case '*' -> leftFloat * rightFloat;
                case '/' -> leftFloat / rightFloat;
                case '+' -> leftFloat + rightFloat;
                case '-' -> leftFloat - rightFloat;
                default -> throw new IllegalArgumentException("Unknown operator \"" + expr.operationOp + "\" for arithmetic expression");
            };
            return res;
        }
        throw new IllegalArgumentException("Type mismatch, got a Boolean and Float in expression :(");
    }

    public void execPrint(AlgebraGrammarASTPrint print) {
        AlgebraGrammarValue val = this.execExpr(print.expr);
        if (val instanceof AlgebraGrammarValueFloat) {
            System.out.println(((AlgebraGrammarValueFloat) val).value);
        }
        else if (val instanceof AlgebraGrammarValueBool) {
            System.out.println(((AlgebraGrammarValueBool) val).value);
        }
    }

    public void execAssign(AlgebraGrammarASTAssign assign) {
        this.varContext.put(assign.value.name, execExpr(assign.expr));
    }

    public void execWhile(AlgebraGrammarASTWhile whl) {
        while (true) {
            // Check condition
            AlgebraGrammarValue cond = execExpr(whl.cond);
            if (!(cond instanceof AlgebraGrammarValueBool)) {
                throw new IllegalArgumentException("Expected Boolean in while but got Float");
            }
            AlgebraGrammarValueBool condBool = (AlgebraGrammarValueBool) cond;
            if (!condBool.value) {
                break;
            }

            // Execute statements
            execAST(whl.exprs);
        }
    }

    public void execIf(AlgebraGrammarASTIf iif) {
        // Yes I know that argument is named poorly, but it's 1 AM so who cares

        // Check condition
        AlgebraGrammarValue cond = execExpr(iif.cond);
        if (!(cond instanceof AlgebraGrammarValueBool)) {
            throw new IllegalArgumentException("Expected Boolean in while but got Float");
        }
        AlgebraGrammarValueBool condBool = (AlgebraGrammarValueBool) cond;
        if (!condBool.value) {
            return;
        }

        // Execute statements
        execAST(iif.exprs);
    }

    public void execStatement(AlgebraGrammarASTStatement statement) {
        if (statement instanceof AlgebraGrammarASTWhile){
            this.execWhile((AlgebraGrammarASTWhile) statement);
        }
        else if (statement instanceof AlgebraGrammarASTIf){
            this.execIf((AlgebraGrammarASTIf) statement);
        }
        else if (statement instanceof AlgebraGrammarASTPrint){
            this.execPrint((AlgebraGrammarASTPrint) statement);
        }
        else if (statement instanceof AlgebraGrammarASTAssign){
            this.execAssign((AlgebraGrammarASTAssign) statement);
        }
    }

    public void execAST(AlgebraGrammarAST ast) {
        if (ast instanceof AlgebraGrammarASTExpressions) {
            AlgebraGrammarASTExpressions exprs = (AlgebraGrammarASTExpressions) ast;
            for (AlgebraGrammarAST i : exprs.statementList) {
                if (i instanceof AlgebraGrammarASTExpr) {
                    this.execExpr((AlgebraGrammarASTExpr) i);
                }
                else if (i instanceof AlgebraGrammarASTStatement) {
                    this.execStatement((AlgebraGrammarASTStatement) i);
                }
            }
        } else {
            System.out.println("AUGH, Y U DO DIS ?!?!");
        }
    }
}
