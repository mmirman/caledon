{-# LANGUAGE
 RecordWildCards,
 TupleSections
 #-}

module Parser where

import AST

import Data.Functor
import Data.Functor.Identity
import Text.Parsec
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

type Parser = ParsecT String ParseState Identity

modifySet :: (S.Set Name -> S.Set Name) -> ParseState -> ParseState
modifySet f s = s { currentSet = f $ currentSet s }

modifyVar :: (Integer -> Integer) -> ParseState -> ParseState
modifyVar f s = s { currentVar = f $ currentVar s }

getNextVar :: Parser String
getNextVar = do
  v <- currentVar <$> getState
  modifyState $ modifyVar (+1)
  return $ show v++"@?_?"

decls :: Parser [Predicate]
decls = do
  whiteSpace
  lst <- many (query <|> defn <?> "declaration")
  eof
  return lst

query :: Parser Predicate
query = do
  reserved "query"
  (nm,ty) <- named dec_pred
  optional semi
  return $ Query nm ty

defn :: Parser Predicate
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

pAtom :: Parser Tm
pAtom =  do reserved "_"
            nm <- getNextVar
            mp <- currentSet <$> getState
            return $ Spine (Var nm) $ Norm <$> Atom <$> var <$> S.toList mp
     <|> do r <- id_var
            return $ var r
     <|> do r <- identifier
            mp <- currentSet <$> getState
            return $ (if S.member r mp then var else cons) r

     <|> (toTm <$> parens tipe)
     <?> "atom"

trm :: Parser Tm
trm =     parens trm
   <|> do reservedOp "λ" <|> reservedOp "\\"
          (nm,tp) <- parens anonNamed <|> anonNamed
          reservedOp "."
          tp' <- tmpState nm trm
          return $ Abs nm tp tp'
   <|> do reservedOp "?λ" <|> reservedOp "?\\"
          (nm,tp) <- parens anonNamed <|> anonNamed
          reservedOp "."
          tp' <- tmpState nm trm
          return $ AbsImp nm tp tp'
   <|> do t <- pAtom
          tps <- many $ (Impl <$> braces tipe)
                 <|> (Norm <$> (parens tipe <|> (Atom <$> pAtom)))
          return $ rebuildSpine t tps
   <?> "term"

fall :: Tp -> Tp -> Tp
fall = Forall ""

fallImp :: Tp -> Tp -> Tp
fallImp = ForallImp ""

table :: OperatorTable String ParseState Identity Tp
table = [ [ binary (reservedOp "->" <|> reservedOp "→") fall AssocRight
          , binary (reservedOp "=>" <|> reservedOp "⇒") fallImp AssocRight
          ]
        , [ binary (reservedOp "<-" <|> reservedOp "←") (flip fall) AssocLeft
          , binary (reservedOp "<=" <|> reservedOp "⇐") (flip fallImp) AssocLeft ]
        ]
  where  binary  name fun assoc = Infix (name >> return fun) assoc

dec_tipe :: (Parser String, String)
dec_tipe = (getId lower, ":")

dec_pred :: (Parser String, String)
dec_pred = (getId lower, "=")

id_var :: Parser String
id_var = getId $ upper <|> char '\''

dec_anon :: (Parser String, String)
dec_anon = (getId $ letter <|> char '\'' , ":")

named :: (Parser a, String) -> Parser (a, Tp)
named (ident, sep) = do
  nm <- ident
  reservedOp sep
  ty <- tipe
  return (nm, ty)

anonNamed :: Parser (String, Tp)
anonNamed = do
  let (ident,sep) = dec_anon
  nm <- ident
  ty <- optionMaybe $ reservedOp sep >> tipe
  nm' <- getNextVar
  mp <- currentSet <$> getState
  return (nm,fromMaybe (Atom $ Spine (Var nm') $ Norm <$> Atom <$> var <$> S.toList mp) ty)

tmpState :: String -> Parser a -> Parser a
tmpState nm m = do
  s <- currentSet <$> getState
  let b = S.member nm s
  modifyState $ modifySet (S.insert nm)
  r <- m
  unless b $ modifyState $ modifySet $ S.delete nm
  return r

tipe :: Parser Tp
tipe = buildExpressionParser table (
        parens tipe
    <|> (Atom <$> trm)
    <|> do (nm,tp) <- brackets anonNamed
           tp' <- tmpState nm tipe
           return $ Forall nm tp tp'
    <|> do (nm,tp) <- braces anonNamed
           tp' <- tmpState nm tipe
           return $ ForallImp nm tp tp'
    <|> do reservedOp "∀" <|> reserved "forall"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ Forall nm tp tp'
    <|> do reservedOp "?∀" <|> reserved "?forall"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ ForallImp nm tp tp'
    <?> "type")

P.TokenParser{..} = P.makeTokenParser $ mydef

mydef :: P.GenLanguageDef String ParseState Identity
mydef = haskellDef
  { P.identStart = lower
  , P.identLetter = alphaNum <|> oneOf "_'-/"
  , P.reservedNames = ["defn", "as", "query", "forall", "?forall", "_"]
  , P.caseSensitive = True
  , P.reservedOpNames = ["->", "=>", "<=", "⇐", "⇒", "→", "<-", "←", ":", "|", "\\","?\\", "λ","?λ","∀","?∀", "."]
  }

getId :: Parser Char -> Parser String
getId start = P.identifier $ P.makeTokenParser $ mydef { P.identStart = start }