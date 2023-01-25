package com.kreog.antlr;

import com.kreog.antlr.java.AlgebraGrammarVisitor;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.Test;

public class AlgebraGrammarParserUnitTest {

    @Test
    public void getNumber() {
        String data = "10;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(10.0 == result);
    }

    @Test
    public void getNegNumber() {
        String data = "-150;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(-150.0 == result);
    }

    @Test
    public void getFloatNumber() {
        String data = "0.25;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(0.25 == result);
    }

    @Test
    public void getNegativeFloatNumber() {
        String data = "-0.25;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(-0.25 == result);
    }

    @Test
    public void getNumberBetweenParenthesis() {
        String data = "(366);";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(366 == result);
    }

    @Test
    public void getNegativeNumberBetweenParenthesis() {
        String data = "(-366);";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(-366 == result);
    }

    @Test
    public void basicAdd() {
        String data = "10000000 + 501283;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(10501283.0 == result);
    }

    @Test
    public void basicSub() {
        String data = "8156415 - 6232415;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(1924000.0 == result);
    }

    @Test
    public void basicDiv() {
        String data = "1268 / 634;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(2.0 == result);
    }

    @Test
    public void basicMul() {
        String data = "3 * 2;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(6.0 == result);
    }

    @Test
    public void basicSpacingHandler() {
        String data = "41                         + 2 +                     45;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(88.0 == result);
    }

    @Test
    public void complexExpression() {
        String data = "(((3 * 2 + 2 / (7 + (13 - 14) + 323 + 1) - 1313) / 83));";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        // lmao that line
        assert(-15.74691 == (double)Math.round(result * 100000d) / 100000d);
    }

    @Test
    public void basicAssignement() {
        String data = "mdr = 4; lol = 5; lol * mdr + mdr;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(24.0 == result);
    }

    @Test
    public void basicPrintStatement() {
        String data = "mdr = 4; lol = 5; ptdr = lol * mdr + mdr; print ptdr;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(24.0 == result);
    }

    @Test
    public void basicPrintStatementExpr() {
        String data = "mdr = 4; lol = 5; ptdr = lol * mdr + mdr; print ptdr + 4 * 11;";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        float result = new AlgebraGrammarVisitor().visit(parser.expressions());
        assert(68.0 == result);
    }
}
