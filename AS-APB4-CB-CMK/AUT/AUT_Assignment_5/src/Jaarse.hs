{-# LANGUAGE LambdaCase #-}

module Jaarse where

import Control.Applicative (Alternative (..))
import Control.Monad (void)
import Data.Char (isAlpha, isDigit, isSpace)
import Data.Functor (void, ($>))

newtype Parser a = Parser {runParser :: String -> Maybe (a, String)}

-- TODO: This has to be redone, as it doesn't work
-- with numbers and special characters
word :: Parser String
word = some letter

oneOf :: [Char] -> Parser Char
oneOf [] = empty
oneOf (a : as) = Parser $ \case
  (c : cs) | c == a -> Just (c, cs)
  c -> runParser (oneOf as) c

-- TODO: Test
noneOf :: [Char] -> Parser Char
noneOf [] = Parser $ \case
  [] -> empty
  c : cs -> Just (c, cs)
noneOf (a : as) = Parser $ \case
  (c : cs) | c == a -> Nothing
  c -> runParser (noneOf as) c

-- TODO: Test
sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p sep = (:) <$> p <*> many (sep *> p)

-- TODO: Test
endBy :: Parser a -> Parser b -> Parser [a]
endBy p sep = many (p <* sep)

skipMany :: Parser a -> Parser ()
skipMany p = void $ many p

skipSpaces :: Parser ()
skipSpaces = skipMany $ oneOf " \t\n"

spaces :: Parser [Char]
spaces = some $ oneOf " \n\t"

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = do
  a <- p
  rest a
  where
    rest a =
      do
        f <- op
        b <- p
        rest $ f a b
        <|> return a

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = do
  a <- p
  rest a
  where
    rest a =
      do
        f <- op
        b <- p
        rest $ f b a
        <|> return a

char :: Char -> Parser Char
char c = anyChar <=> (== c)

nat :: Parser Integer
nat = read <$> some digit

pluses :: Parser String
pluses = many plus

plus :: Parser Char
plus = char '+'

lexeme :: Parser a -> Parser a
lexeme a = a <* skipSpaces

negFloat :: Parser Float
negFloat = negate <$> lexeme (char '-' *> float)

-- TODO: Find a better way to do this, case do blocks are ugly
posFloat :: Parser Float
posFloat = do
  skipSpaces
  intPart <- some digit
  point
  decPart <- some digit
  skipSpaces
  return $ read $ intPart ++ "." ++ decPart

float :: Parser Float
float =
  plus *> float
    <|> negFloat
    <|> posFloat

option :: a -> Parser a -> Parser a
option a p = Parser $ \s -> case runParser p s of
  Nothing -> Just (a, s)
  Just (x, s') -> Just (x, s')

optional :: Parser a -> Parser ()
optional p = option () (p $> ())

between :: Parser open -> Parser close -> Parser a -> Parser a
between open close p = lexeme open *> p <* lexeme close

point :: Parser Char
point = char '.'

digits :: Parser String
digits = some digit

anyChar :: Parser Char
anyChar = Parser $ \case
  [] -> Nothing
  (c : cs) -> Just (c, cs)

digit :: Parser Char
digit = anyChar <=> isDigit

letter :: Parser Char
letter = anyChar <=> isAlpha

(<=>) :: Parser a -> (a -> Bool) -> Parser a
p <=> f = Parser $ \s -> case runParser p s of
  Nothing -> Nothing
  Just (a, s') -> if f a then Just (a, s') else Nothing

instance Applicative Parser where
  pure a = Parser $ \s -> Just (a, s)
  (Parser f) <*> (Parser g) = Parser $ \s -> case f s of
    Nothing -> Nothing
    Just (f', s') -> case g s' of
      Nothing -> Nothing
      Just (g', s'') -> Just (f' g', s'')

instance Functor Parser where
  fmap f (Parser p) = Parser $ \s -> case p s of
    Nothing -> Nothing
    Just (a, s') -> Just (f a, s')

instance Monad Parser where
  return = pure
  (Parser f) >>= g = Parser $ \s -> case f s of
    Nothing -> Nothing
    Just (r, s') -> runParser (g r) s'

instance Alternative Parser where
  empty = Parser $ const Nothing
  (Parser f) <|> (Parser g) = Parser $ \s -> case f s of
    Nothing -> g s
    res -> res