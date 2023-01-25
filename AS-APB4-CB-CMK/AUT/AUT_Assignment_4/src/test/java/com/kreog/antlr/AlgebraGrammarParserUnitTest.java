package com.kreog.antlr;

import com.kreog.antlr.java.AlgebraGrammarVisitor;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Test;

import com.kreog.antlr.java.AlgebraGrammarAST;
import com.kreog.antlr.java.AlgebraGrammarExecutor;
import com.kreog.antlr.java.AlgebraGrammarValueFloat;

public class AlgebraGrammarParserUnitTest {

    @Test
    public void fibonacci() {
        String data = """
            fibo = (i) {
                a = 0;
                b = 1;
                c = 1;
                while (i != 1) {
                    c = a + b;
                    a = b;
                    b = c;
                    i = i - 1;
                };
                return b;
            };

            return fibo(10);
        """;
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        AlgebraGrammarAST ast = new AlgebraGrammarVisitor().visit(parser.expressions());
        AlgebraGrammarExecutor executor = new AlgebraGrammarExecutor();
        var res = (AlgebraGrammarValueFloat) executor.execAST(ast);
        assert(res.value.equals(55f));
    }

    @Test
    public void fibonacci_rec() {
        String data = """
            fibo = (x) {
                return if (x == 1) {
                    return 1;
                } else {
                    return if (x == 2) {
                        return 1;
                    } else {
                        return fibo(x - 1) + fibo(x - 2);
                    };
                };
            };

            return fibo(10);
        """;
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        AlgebraGrammarAST ast = new AlgebraGrammarVisitor().visit(parser.expressions());
        AlgebraGrammarExecutor executor = new AlgebraGrammarExecutor();
        var res = (AlgebraGrammarValueFloat) executor.execAST(ast);
        assert(res.value.equals(55f));
    }

    @Test
    public void first_class_function() {
        String data = """
            a = () {
                return 7;
            };

            b = (x) {
                return x() * 6;
            };

            return b(a);
        """;
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        AlgebraGrammarAST ast = new AlgebraGrammarVisitor().visit(parser.expressions());
        AlgebraGrammarExecutor executor = new AlgebraGrammarExecutor();
        var res = (AlgebraGrammarValueFloat) executor.execAST(ast);
        assert(res.value.equals(42f));
    }
}
