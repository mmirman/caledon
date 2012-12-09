{-# LANGUAGE RecordWildCards, TupleSections #-}
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
import Data.Maybe
import qualified Text.Parsec.Token as P
import qualified Data.Set as S

-----------------------------------------------------------------------
-------------------------- PARSER -------------------------------------
-----------------------------------------------------------------------

data ParseState = ParseState { currentVar :: Integer, currentSet :: S.Set Name }

modifySet f s = s { currentSet = f $ currentSet s }
modifyVar f s = s { currentVar = f $ currentVar s }

getNextVar = do
  v <- currentVar <$> getState
  modifyState $ modifyVar (+1)
  return $ show v++"@?_?"

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

pAtom =  do reserved "_"
            nm <- getNextVar
            return $ var nm
     <|> do r <- id_var
            return $ var r
     <|> do r <- identifier
            mp <- currentSet <$> getState 
            return $ (if S.member r mp then var else cons) r

     <|> (tpToTm <$> parens tipe)
     <?> "atom"
  
trm =  parens trm 
   <|> do reservedOp "λ" <|> reservedOp "\\"
          (nm,tp) <- parens anonNamed <|> anonNamed
          reservedOp "."
          tp' <- tmpState nm trm
          return $ AbsImp nm tp tp'
   <|> do reservedOp "?λ" <|> reservedOp "?\\"
          (nm,tp) <- parens anonNamed <|> anonNamed
          reservedOp "."
          tp' <- tmpState nm trm
          return $ Abs nm tp tp'          
   <|> do t <- pAtom
          tps <- many $ (parens tipe) <|> (Atom <$> pAtom)
          return $ rebuildSpine t tps
   <?> "term"

fall = Forall ""
fallImp = ForallImp ""

table = [ [ binary (reservedOp "->" <|> reservedOp "→") fall AssocRight
          , binary (reservedOp "=>" <|> reservedOp "⇒") fallImp AssocRight
          ] 
        , [ binary (reservedOp "<-" <|> reservedOp "←") (flip fall) AssocLeft
          , binary (reservedOp "<=" <|> reservedOp "⇐") (flip fallImp) AssocLeft ]
        ]
  where  binary  name fun assoc = Infix (name >> return fun) assoc
         
 
dec_tipe = (getId lower, ":")
dec_pred = (getId lower, "=")
id_var = getId $ upper <|> char '\''
dec_anon = (getId $ letter <|> char '\'' , ":")

named (ident, sep) = do
  nm <- ident
  reservedOp sep
  ty <- tipe
  return (nm, ty)

anonNamed = do
  let (ident,sep) = dec_anon 
  nm <- ident
  ty <- optionMaybe $ reservedOp sep >> tipe
  nm' <- getNextVar
  return (nm,fromMaybe (Atom $ var nm') ty)

tmpState nm m = do
  s <- currentSet <$> getState
  let b = S.member nm s
  modifyState $ modifySet (S.insert nm)
  r <- m
  unless b $ modifyState $ modifySet $ S.delete nm
  return r

tipe = buildExpressionParser table ( 
        parens tipe
    <|> (Atom <$> trm)
    <|> do (nm,tp) <- brackets anonNamed 
           tp' <- tmpState nm tipe
           return $ Forall nm tp tp'
    <|> do reservedOp "∀" <|> reserved "forall"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ Forall nm tp tp'
    <|> do (nm,tp) <- braces anonNamed 
           tp' <- tmpState nm tipe
           return $ ForallImp nm tp tp'           
    <|> do reservedOp "?∀" <|> reserved "?forall"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ ForallImp nm tp tp'     
           
    <?> "type")
           
P.TokenParser{..} = P.makeTokenParser $ mydef
mydef = haskellDef 
 { P.identStart = lower
 , P.identLetter = alphaNum <|> oneOf "_'-/"
 , P.reservedNames = ["defn", "as", "query", "forall", "?forall", "_"]
 , P.caseSensitive = True
 , P.reservedOpNames = ["->", "=>", "<=", "⇐", "⇒", "→", "<-", "←", ":", "|", "\\", "λ","?\\", "?λ", "∀", "?∀", "."]
 }
getId start = P.identifier $ P.makeTokenParser $ mydef { P.identStart = start }
