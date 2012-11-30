{-# LANGUAGE RecordWildCards #-}
module Parser where

import AST
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
  (nm,ty) <- named dec_pred
  optional semi
  return $ Query nm ty

defn =  do
  reserved "defn" 
  (nm,ty) <- named dec_tipe
  let more =  do reserved "as"
                 lst <- flip sepBy1 (reservedOp "|") $ named dec_pred
                 optional semi
                 return $ Predicate nm ty lst
      none = do optional semi
                return $ Predicate nm ty []
  more <|> none <?> "definition"

atom =  do r <- id_var
           return $ Var r
    <|> do r <- identifier
           mp <- getState 
           return $ (if S.member r mp then Var else Cons) r
    <|> (tpToTm <$> parens tipe)
    <?> "atom"
  
trm =  parens trm 
   <|> do t <- atom
--          tl <- many $ (flip TyApp <$> braces tipe) <|> (flip App <$> (atom <|> parens trm))
          tl <- many $ (flip TyApp <$> parens tipe) <|> (flip TyApp <$> Atom <$> atom)
          return $ foldl (flip ($)) t tl 
   <?> "term"

imp = Forall ""

table = [ [binary "->" imp {- (:->:) -} AssocRight] 
        , [binary "<-" (flip imp {- (:->:) -}) AssocLeft] 
        ]
  where  binary  name fun assoc = Infix (reservedOp name >> return fun) assoc
         
 
dec_tipe = (getId lower, ":")
dec_pred = (getId lower, "=")
id_var = getId $ upper <|> char '\''
dec_anon = (getId $ letter <|> char '\'' , ":")

named (ident, sep) = do
  nm <- ident
  reservedOp sep
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
    <|> (Atom <$> trm)
    <|> do (nm,tp) <- brackets $ named dec_anon
           optional $ reservedOp "->"
           tp' <- tmpState nm tipe
           return $ Forall nm tp tp'
    <?> "type")
           
P.TokenParser{..} = P.makeTokenParser $ mydef
mydef = haskellDef 
 { P.identStart = lower
 , P.identLetter = alphaNum <|> oneOf "_'-/"
 , P.reservedNames = ["defn", "as", "query", "forall", "exists"]
 , P.caseSensitive = True
 , P.reservedOpNames = ["->", "<-", ":", "|"]
 }
getId start = P.identifier $ P.makeTokenParser $ mydef { P.identStart = start }
