package com.kreog.antlr;

import com.kreog.antlr.AlgebraGrammarLexer;

import com.kreog.antlr.java.AlgebraGrammarListener;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTreeWalker;
import org.junit.Test;

public class AlgebraGrammarParserUnitTest {

    @Test
    public void getNumber() {
        String data = "10";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(10.0 == listener.getResult());
    }

    @Test
    public void getNegNumber() {
        String data = "-150";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(-150.0 == listener.getResult());
    }

    @Test
    public void getSimplifiedFloatNumber() {
        String data = ".1";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(0.1 == listener.getResult());
    }

    @Test
    public void getFloatNumber() {
        String data = "0.25";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(0.25 == listener.getResult());
    }

    @Test
    public void getNegativeFloatNumber() {
        String data = "-0.25";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(-0.25 == listener.getResult());
    }

    @Test
    public void getNumberBetweenParenthesis() {
        String data = "(366)";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(366 == listener.getResult());
    }

    @Test
    public void getNegativeNumberBetweenParenthesis() {
        String data = "(-366)";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(-366 == listener.getResult());
    }

    @Test
    public void basicAdd() {
        String data = "10000000 + 501283";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(10501283.0 == listener.getResult());
    }

    @Test
    public void basicSub() {
        String data = "8156415 - 6232415";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(1924000.0 == listener.getResult());
    }

    @Test
    public void basicDiv() {
        String data = "1268 / 634";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(2.0 == listener.getResult());
    }

    @Test
    public void basicMul() {
        String data = "3 * 2";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(6.0 == listener.getResult());
    }

    @Test
    public void basicSpacingHandler() {
        String data = "41                         + 2 +                     45";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        assert(88.0 == listener.getResult());
    }

    @Test
    public void complexExpression() {
        String data = "(((3 * 2 + 2 / (7 + (13 - 14) + 323 + 1) - 1313) / 83))";
        AlgebraGrammarLexer lexer = new AlgebraGrammarLexer(CharStreams.fromString(data));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        AlgebraGrammarParser parser = new AlgebraGrammarParser(tokens);
        final AlgebraGrammarListener listener = new AlgebraGrammarListener();
        new ParseTreeWalker().walk(listener, parser.expression());
        // lmao that line
        assert(-15.74691 == (double)Math.round(listener.getResult() * 100000d) / 100000d);
    }
}
