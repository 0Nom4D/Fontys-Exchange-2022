package com.kreog.antlr;

import com.kreog.antlr.java.AlgebraGrammarVisitor;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Test;

import com.kreog.antlr.java.AlgebraGrammarAST;
import com.kreog.antlr.java.AlgebraGrammarExecutor;

public class AlgebraGrammarParserUnitTest {

    @Test
    public void fibonacci() {
        String data = """
            a = 0;
            b = 1;
            c = 1;
            i = 50;
            print b;
            while (i != 0) {
                c = a + b;
                a = b;
                b = c;
                print b;
                i = i - 1;
            };
        """;
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        AlgebraGrammarAST ast = new AlgebraGrammarVisitor().visit(parser.expressions());
        AlgebraGrammarExecutor executor = new AlgebraGrammarExecutor();
        executor.execAST(ast);
    }
}
