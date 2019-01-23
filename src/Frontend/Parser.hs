{-# LANGUAGE ScopedTypeVariables, AllowAmbiguousTypes #-}
module Frontend.Parser where

import Prelude hiding (noneOf)
-- import Text.Megaparsec hiding (some,many)
-- import Text.Megaparsec.Char
-- import qualified Text.Megaparsec.Lexer as L
import qualified Data.Text as T
import Frontend.Expr
import Text.Parsix hiding (spanned,Parser)
import qualified Text.Parsix.Parser.Internal
import qualified Text.Parsix
import Control.DeepSeq
import Frontend.Indentation

type Parser = IndentT Text.Parsix.Parser

parseTextRel :: Parser a -> Text -> FilePath -> Position -> Result a
parseTextRel p inp file (Position _ x y) = case runIndentT p of
  Text.Parsix.Parser.Internal.Parser p' -> p'
    (\res _ -> Success res)
    (\res _ _pos _hl -> Success res)
    (\err -> Failure $ Error err pos' inp mempty file)
    (\err pos hl -> Failure $ Error err pos inp hl file)
    pos'
    mempty
    inp
    where pos' = Position 0 x y

-- top-level syntax deals w/ level-polymorphism is f_{i j k} args = body
-- TODO: comments
-- TODO: should we let macros parse comments or strip them first?

instance IsString s => IsString (Text.Parsix.Parser s) where
  fromString s = (fromString <$> string s) <* many (char ' ')
instance IsString s => IsString (Parser s) where
  fromString s = (fromString <$> string s) <* spc

-- TODO: remove auto whitespace from CharParsing (IndentT m),
-- & make a newtype wrapper for it

spc :: TokenParsing m => m ()
spc = someSpace -- (do
  -- many (char ' ')
  -- optional (char '\n' *> continuedI) -- $ many (oneOf " ")
  -- pure ()) <?> "whitespace"
  -- spc = L.space (spaceChar >> pure ()) lineCmnt blockCmnt
  -- where lineCmnt  = L.skipLineComment "#"
  --       blockCmnt = empty -- L.skipBlockComment "/*" "*/"

word :: _ => m T.Text
word = try (((T.pack <$> some (alphaNum <|> oneOf ("_" :: String)) <?> "variable") <* spc) >>=
  \nm -> if nm `elem` ["where","->",":","of"] then unexpected $ T.unpack nm else pure nm)

definition :: Parser (Definition,Span)
definition = hanging $ spanned (flip (,)) ((Definition
  <$> (T.pack <$> some alphaNum)
  <*> (optional ("_{" *> many word <* "}") <* spc)
  <*> optional (":" *> expr)
  <*> ("=" *> expr)) <|> (MacroD <$> macro))

defns :: Parser [(Definition,Span)]
defns = many (oneOf [' ','\n']) *> many (definition <* many (oneOf [' ','\n']))

-- problem:
-- ambiguity on `(x : a) (y : b) -> c`
-- could be app & one pi or two pis
-- more obvious with `a (b : c) -> d`
-- TODO: maybe have different pi syntax to avoid this?

expr :: Parser Expr'
expr =
  spanned (flip (:~)) (
      (try (Pi <$> some (spanned (&) piTele) <* "->" <*> expr) <?> "pi")
  <|> (try ((\(s,x) y -> Arr x y) <$> spanned (,) expr' <* spc <* "->" <*> expr) <?> "arrow")
  <|> (try (ConstraintArr <$> expr' <* spc <* "=>" <*> expr) <?> "constraint context")
      ) <|> spanned (&) (app <$> some (expr'))
      where
    piTele = ("(" *> (flip2 (,Explicit,,) <$> word <* ":" <*> expr) <* ")")
         <|> ("{" *> (flip2 (,Implicit,,) <$> word <* ":" <*> expr) <* "}")
    app [x] _ = x
    app l s = App l :~ s


expr' :: Parser Expr'
expr' = spanned (flip (:~)) (
        (MacroE <$> macro) 
    <|> (Underscore <$ ("_" *> spc))
    <|> (Var <$> word)
    -- <|> (some (telescopeElem expr))
    <|> ("\\" *> (Lam <$> some (spanned (&) lamTele) <* "->" <*> expr) <?> "lambda")
    <|> ("(" *> (Parens <$> expr) <* ")" <?> "parens")
    )
  where
    -- lamTele :: m Parser (Span -> (Span,Text,Maybe Expr'))
    lamTele =
          (pure (flip2 (,,)) <* "(" <*> word <* ":" <*> (Just <$> expr) <* ")")
      <|> (flip (,,Nothing) <$> word)

flip2 f a b c = f c a b

spanned :: SliceParsing f => (Span -> x -> a) -> f x -> f a
spanned f x = (uncurry f) <$> Text.Parsix.spanned x

macro :: Parser MacroCall
macro = "[" *> unindent (MacroCall
  <$> expr
  -- TODO: remove try?
  <*> (optional (try ("|" *> spanned (,) (T.pack <$> go 0)))) <?> "macro") <* "]" where
  go :: Int -> Parser String
  go n = ((:) <$> noneOf ['[',']'] <*> go n)
     <|> ((:) <$> char '[' <*> go (n+1))
     <|> (if n > 0 then ((:) <$> char ']' <*> go (n-1)) else empty)
     <|> (if n == 0 then pure [] else empty)

-- file :: Parser [Definition]
-- file = 


