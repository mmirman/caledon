{-# LANGUAGE RecordWildCards #-}
module Parser where

import Unifier 
import Choice

import Data.Foldable as F (msum, forM_)
import Data.Functor
import Text.Parsec.String
import Text.Parsec
import Data.Monoid
import Control.Monad (unless)
import Text.Parsec.Language (haskellDef)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P
import qualified Data.Set as S

-----------------------------------------------------------------------
-------------------------- PARSER -------------------------------------
-----------------------------------------------------------------------
decls = do
  whiteSpace
  lst <- many (query <|> defn <?> "declaration")
  eof
  return lst

query = do 
  reserved "query" 
  (nm,ty) <- namedTipe "="
  optional semi
  return $ Query nm ty

defn =  do
  reserved "defn" 
  (nm,ty) <- namedTipe ":"
  let more =  do reserved "as"
                 lst <- flip sepBy1 (reserved "|") $ namedTipe "="
                 optional semi
                 return $ Predicate nm ty lst
      none = do optional semi
                return $ Predicate nm ty []
  more <|> none <?> "definition"

atom =  do c <- oneOf "\'"
           r <- identifier
           return $ Var $ c:r
    <|> do r <- identifier
           mp <- getState 
           return $ (if S.member r mp then Var else Cons) r
    <|> (tpToTm <$> parens tipe)
    <?> "atom"
  
trm =  parens trm 
   <|> do t <- atom
          tl <- many $ (flip TyApp <$> braces tipe) <|> (flip App <$> (atom <|> parens trm))
          return $ foldl (flip ($)) t tl 
   <?> "term"

table = [ [binary "->" (:->:) AssocRight] 
        , [binary "<-" (flip (:->:)) AssocLeft] 
        ]
  where  binary  name fun assoc = Infix (reservedOp name >> return fun) assoc
         
namedTipe c = do nm <- identifier
                 reserved c
                 ty <- tipe
                 return (nm, ty)
               
tmpState nm m = do
  s <- getState
  let b = S.member nm s
  putState $ S.insert nm s
  r <- m
  unless b $ modifyState (S.delete nm)
  return r

tipe = buildExpressionParser table ( 
        parens tipe
    <|> (Atom False <$> trm)
    <|> do (nm,tp) <- brackets $ namedTipe ":"
           tp' <- tmpState nm tipe
           return $ Forall nm tp tp'
    <|> do (nm,tp) <- braces $ namedTipe ":"
           tp' <- tmpState nm tipe
           return $ Exists nm tp tp'
    <?> "type")
           
P.TokenParser{..} = P.makeTokenParser $ haskellDef 
 { P.identStart = letter
 , P.identLetter = alphaNum <|> oneOf "_'-/"
 , P.reservedNames = ["defn", "as", "query", "=", ":", "|", "forall", "exists"]
 , P.caseSensitive = True
 , P.reservedOpNames = ["->", "<-"]
 }