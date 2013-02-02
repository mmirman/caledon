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
  (nm,ty) <- named decPred
  optional semi
  return $ Query nm ty

defn :: Parser Predicate
defn =  do
  reserved "defn"
  (nm,ty) <- named decTipe
  let more =  do reserved "as"
                 lst <- flip sepBy1 (reservedOp "|") $ named decPred
                 optional semi
                 return $ Predicate nm ty lst
      none = do optional semi
                return $ Predicate nm ty []
  more <|> none <?> "definition"

pAtom :: Parser Spine
pAtom =  do reserved "_"
            nm <- getNextVar
            mp <- currentSet <$> getState
            return $ Spine nm $ var <$> S.toList mp
     <|> do r <- idVar
            return $ var r
     <|> do r <- identifier
            mp <- currentSet <$> getState
            return $ var r

     <|> (parens tipe)
     <?> "atom"

trm :: Parser Term
trm =     parens trm
--   <|> Spine "#open#" <$> (:[]) <$> angles trm
          
   <|> do reservedOp "λ" <|> reservedOp "\\"
          (nm,tp) <- parens anonNamed <|> anonNamed
          reservedOp "."
          tp' <- tmpState nm trm
          return $ Abs nm tp tp'
{-   <|> do reservedOp "?λ" <|> reservedOp "?\\"
          (nm,tp) <- parens anonNamed <|> anonNamed
          reservedOp "."
          tp' <- tmpState nm trm
          return $ AbsImp nm tp tp' -}
   <|> do t <- pAtom
          tps <- many $ parens tipe <|> pAtom
          return $ rebuildSpine t tps
   <?> "term"


table :: OperatorTable String ParseState Identity Type
table = [ [ binary (reservedOp "->" <|> reservedOp "→") (~>) AssocRight
--          , binary (reservedOp "=>" <|> reservedOp "⇒") fallImp AssocRight
          ]
        , [ binary (reservedOp "<-" <|> reservedOp "←") (flip (~>)) AssocLeft
--          , binary (reservedOp "<=" <|> reservedOp "⇐") (flip fallImp) AssocLeft ]
          ]]
  where binary name fun = Infix (name >> return fun)

decTipe :: (Parser String, String)
decTipe = (getId lower, ":")

decPred :: (Parser String, String)
decPred = (getId lower, "=")

idVar :: Parser String
idVar = getId $ upper <|> char '\''

decAnon :: (Parser String, String)
decAnon = (getId $ letter <|> char '\'' , ":")

named :: (Parser a, String) -> Parser (a, Type)
named (ident, sep) = do
  nm <- ident
  reservedOp sep
  ty <- tipe
  return (nm, ty)

anonNamed :: Parser (String, Type)
anonNamed = do
  let (ident,sep) = decAnon
  nm <- ident
  ty <- optionMaybe $ reservedOp sep >> tipe
  nm' <- getNextVar
  nm'' <- getNextVar
  return (nm,fromMaybe (infer nm' atom $ infer nm'' (var nm') $ var nm'') ty)

tmpState :: String -> Parser a -> Parser a
tmpState nm m = do
  s <- currentSet <$> getState
  let b = S.member nm s
  modifyState $ modifySet (S.insert nm)
  r <- m
  unless b $ modifyState $ modifySet $ S.delete nm
  return r

tipe :: Parser Type
tipe = buildExpressionParser table (
        parens tipe
    <|> trm
    <|> do (nm,tp) <- brackets anonNamed
           tp' <- tmpState nm tipe
           return $ forall nm tp tp'
    <|> do (nm,tp) <- braces anonNamed
           tp' <- tmpState nm tipe
           return $ exists nm tp tp' 
           
    <|> do (nm,tp) <- angles anonNamed
           tp' <- tmpState nm tipe
           return $ infer nm tp tp'
           
    <|> do reservedOp "∀" <|> reserved "forall"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ forall nm tp tp'

    <|> do reservedOp "??" <|> reserved "infer"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ infer nm tp tp'           
    <?> "type")

P.TokenParser{..} = P.makeTokenParser mydef

mydef :: P.GenLanguageDef String ParseState Identity
mydef = haskellDef
  { P.identStart = lower
  , P.identLetter = alphaNum <|> oneOf "_'-/"
  , P.reservedNames = ["defn", "as", "query", "forall", "exists", "?forall", "_", "infer"]
  , P.caseSensitive = True
  , P.reservedOpNames = ["->", "=>", "<=", 
                         "⇐", "⇒", "→", "<-", 
                         "←", ":", "|", 
                         "\\", "?\\", 
                         "λ","?λ", 
                         "∀", "?∀", 
                         "??", "∃", "."]
  }

getId :: Parser Char -> Parser String
getId start = P.identifier $ P.makeTokenParser mydef { P.identStart = start }