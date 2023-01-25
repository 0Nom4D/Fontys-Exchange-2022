module Parsing where

import Control.Applicative
import Jaarse

data Datum
  = Atom String
  | List [Datum]
  | Sat Datum
  | DString String

instance Show Datum where
  show (Atom name) = name
  show (List contents) = "(" ++ unwordsList contents ++ ")"
  show (DString content) = "\"" ++ content ++ "\""
  show (Sat content) = "sat : " ++ show content

commonList :: Parser Datum
commonList = lexeme . between (char '(') (char ')') $ list

symbol :: Parser Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_-~"

atom :: Parser Datum
atom = Atom <$> some (letter <|> digit <|> symbol)

string :: Parser Datum
string = do
  x <- between (char '"') (char '"') (many (noneOf "\""))
  return $ DString x

expr :: Parser Datum
expr =
  atom
    <|> string
    <|> commonList

exprs :: Parser [Datum]
exprs = lexeme . many . lexeme $ expr

-- TODO: Test
list :: Parser Datum
list = List <$> many (lexeme expr)

sat :: Parser Datum
sat = Sat <$> atom *> commonList

unwordsList :: Show a => [a] -> String
unwordsList = unwords . map show
