package com.kreog.antlr.java;

import java.util.HashMap;
import java.util.stream.IntStream; 

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
        else if (expr instanceof AlgebraGrammarASTFunction) {
            AlgebraGrammarASTFunction func = (AlgebraGrammarASTFunction) expr;
            AlgebraGrammarValueFunction funcValue = new AlgebraGrammarValueFunction();
            for (AlgebraGrammarASTAtom i : func.parameters) {
                funcValue.parameters.add(i.name);
            }
            funcValue.exprs = func.statements;
            return funcValue;
        }
        else if (expr instanceof AlgebraGrammarASTCall) {
            AlgebraGrammarASTCall call = (AlgebraGrammarASTCall) expr;
            AlgebraGrammarValue funcVal = execExpr(call.name);
            if (funcVal instanceof AlgebraGrammarValueFunction) {
                AlgebraGrammarValueFunction func = (AlgebraGrammarValueFunction) funcVal;
                // Create a new Executor, and copy the context to it
                AlgebraGrammarExecutor funcExecutor = new AlgebraGrammarExecutor();
                funcExecutor.varContext.putAll(varContext);

                // Copy over the arguments (Arguments can shadow previous locals)
                if (func.parameters.size() != call.params.size()) {
                    throw new IllegalArgumentException("Expected " + func.parameters.size() + " arguments but got " + call.params.size());
                }

                // I use parallel because I could, and it's kinda funny.
                // To be more serious parallel is 100% usable since the
                // only things that are done in parallel are expressions
                // and since expressions don't have side effects at all
                // we can multi thread without caring about anything.
                // And yes that means all functions are pure, because
                // why the hell not, functional programming is cool ;)
                // IntStream.range(0, func.parameters.size()).parallel().forEach(n -> {
                //     funcExecutor.varContext.put(func.parameters.get(n), execExpr(call.params.get(n)));
                // });

                // Well it wasn't faster from testing so back to a good ol' for loop xd
                for (int i = 0; i < func.parameters.size(); i++) {
                    funcExecutor.varContext.put(func.parameters.get(i), execExpr(call.params.get(i)));
                }

                // Call function
                return funcExecutor.execAST(func.exprs);
            }
            throw new IllegalAccessError("Something that is not a function tried to get called! (How do you do that??)");
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

    public AlgebraGrammarValue execPrint(AlgebraGrammarASTPrint print) {
        AlgebraGrammarValue val = this.execExpr(print.expr);
        if (val instanceof AlgebraGrammarValueFloat) {
            System.out.println(((AlgebraGrammarValueFloat) val).value);
        }
        else if (val instanceof AlgebraGrammarValueBool) {
            System.out.println(((AlgebraGrammarValueBool) val).value);
        }
        return new AlgebraGrammarValueVoid();
    }

    public AlgebraGrammarValue execAssign(AlgebraGrammarASTAssign assign) {
        this.varContext.put(assign.value.name, execExpr(assign.expr));
        return new AlgebraGrammarValueVoid();
    }

    public AlgebraGrammarValue execWhile(AlgebraGrammarASTWhile whl) {
        while (true) {
            // Check condition
            AlgebraGrammarValue cond = execExpr(whl.cond);
            if (!(cond instanceof AlgebraGrammarValueBool)) {
                throw new IllegalArgumentException("Expected Boolean in while but got Float");
            }
            AlgebraGrammarValueBool condBool = (AlgebraGrammarValueBool) cond;
            if (!condBool.value) {
                return new AlgebraGrammarValueVoid();
            }

            // Execute statements
            var ret = execAST(whl.exprs);
            if (!(ret instanceof AlgebraGrammarValueVoid)) {
                return ret;
            }
        }
    }

    public AlgebraGrammarValue execIf(AlgebraGrammarASTIf iif) {
        // Yes I know that argument is named poorly, but it's 1 AM so who cares

        // Check condition
        AlgebraGrammarValue cond = execExpr(iif.cond);
        if (!(cond instanceof AlgebraGrammarValueBool)) {
            throw new IllegalArgumentException("Expected Boolean in while but got Float");
        }
        AlgebraGrammarValueBool condBool = (AlgebraGrammarValueBool) cond;
        if (!condBool.value) {
            return execAST(iif.right);
        }

        // Execute statements
        return execAST(iif.left);
    }

    public AlgebraGrammarValue execStatement(AlgebraGrammarASTStatement statement) {
        if (statement instanceof AlgebraGrammarASTWhile){
            return this.execWhile((AlgebraGrammarASTWhile) statement);
        }
        else if (statement instanceof AlgebraGrammarASTIf){
            return this.execIf((AlgebraGrammarASTIf) statement);
        }
        else if (statement instanceof AlgebraGrammarASTPrint){
            return this.execPrint((AlgebraGrammarASTPrint) statement);
        }
        else if (statement instanceof AlgebraGrammarASTAssign){
            return this.execAssign((AlgebraGrammarASTAssign) statement);
        }
        return new AlgebraGrammarValueVoid();
    }

    public AlgebraGrammarValue execAST(AlgebraGrammarAST ast) {
        if (ast instanceof AlgebraGrammarASTExpressions) {
            AlgebraGrammarASTExpressions exprs = (AlgebraGrammarASTExpressions) ast;
            for (AlgebraGrammarAST i : exprs.statementList) {
                if (i instanceof AlgebraGrammarASTExpr) {
                    this.execExpr((AlgebraGrammarASTExpr) i);
                }
                else if (i instanceof AlgebraGrammarASTReturn) {
                    var expr = ((AlgebraGrammarASTReturn) i).expr;
                    if (expr instanceof AlgebraGrammarASTExpr) {
                        return this.execExpr((AlgebraGrammarASTExpr) expr);
                    }
                    else if (expr instanceof AlgebraGrammarASTStatement) {
                        return this.execStatement((AlgebraGrammarASTStatement) expr);
                    }
                }
                else if (i instanceof AlgebraGrammarASTStatement) {
                    this.execStatement((AlgebraGrammarASTStatement) i);
                }
            }
        }
        return new AlgebraGrammarValueVoid();
    }
}
