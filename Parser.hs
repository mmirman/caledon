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
import Data.List
import Data.Maybe
import qualified Text.Parsec.Token as P
import qualified Data.Set as S

-----------------------------------------------------------------------
-------------------------- PARSER -------------------------------------
-----------------------------------------------------------------------

data ParseState = ParseState { currentVar :: Integer, currentSet :: S.Set Name, currentTable :: FixityTable }

type Parser = ParsecT String ParseState Identity

modifySet :: (S.Set Name -> S.Set Name) -> ParseState -> ParseState
modifySet f s = s { currentSet = f $ currentSet s }

modifyVar :: (Integer -> Integer) -> ParseState -> ParseState
modifyVar f s = s { currentVar = f $ currentVar s }

getNextVar :: Parser String
getNextVar = do
  v <- currentVar <$> getState
  modifyState $ modifyVar (+1)
  return $ show v

decls :: Parser [Predicate]
decls = do
  whiteSpace
  lst <- many (topLevel <?> "declaration")
  eof
  return lst

topLevel = fixityDef <|> query <|> defn <|> letbe

data Fixity = FixLeft | FixRight | FixNone

data FixityTable = FixityTable { fixityLeft :: [(Integer,String)] 
                               , fixityNone :: [(Integer, String)]
                               , fixityRight :: [(Integer, String)]
                               } deriving (Show)

emptyTable = FixityTable [] [] []

fixityDef = do 
  -- I wish template haskell worked with record wild cards!
  (setFixity) <- (reserved "infixl" >> return (\b c -> b { fixityLeft = c $ fixityLeft b} )) 
             <|> (reserved "infix" >> return (\b c -> b { fixityNone = c $ fixityNone b}))
             <|> (reserved "infixr" >> return (\b c -> b { fixityRight = c $ fixityRight b}))
  n <- integer
  op <- operator
  
  let modify = insertBy (\(n,_) (m,_) -> compare n m) (n,op)
  modifyState $ \b -> b { currentTable = setFixity (currentTable b) modify }
  topLevel
  

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
  
letbe :: Parser Predicate
letbe =  do
  reserved "let"
  (nm,ty) <- named decTipe
  reserved "be"
  val <- tipe
  return (Define nm val ty) <?> "definition"  




decTipe :: (Parser String, String)
decTipe = (operator <|> getId lower, ":")

decPred :: (Parser String, String)
decPred = (operator <|> getId lower, "=")

idVar :: Parser String
idVar = getId $ upper <|> char '\''

decVar :: (Parser String, String)
decVar = (idVar <|> getId lower, "=")

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


table :: OperatorTable String ParseState Identity Type
table = [ [lam]
          , [ binary (reservedOp "->" <|> reservedOp "→") (forall) AssocRight
          , binary (reservedOp "=>" <|> reservedOp "⇒") (imp_forall) AssocRight
          ]
        , [ binary (reservedOp "<-" <|> reservedOp "←") (flip . forall) AssocLeft
          , binary (reservedOp "<=" <|> reservedOp "⇐") (flip . imp_forall) AssocLeft 
          ]
        ]
  where binary name fun = Infix $ do 
          name
          fun <$> getNextVar
        lam = Postfix $ do
          reservedOp "λ" <|> reservedOp "\\"
          (nm,tp) <- parens anonNamed <|> anonNamed
          reservedOp "."
          return $ Abs nm tp
          
tipe = do
  FixityTable left none right <- currentTable <$> getState 
  
  let getSnd [] = []
      getSnd (a:l) = l
      getFst (a:l) = a
      getFst [] = []
                  
      union [] [] [] = []
      union l1 l2 l3 = (getFst l1++getFst l2++getFst l3):union (getSnd l1) (getSnd l2) (getSnd l3)
      
      reify ((a,op):(a',op'):l) r | a == a' = reify ((a',op'):l) (op:r)
      reify ((a,op):l) r = (op:r):reify l []
      reify [] [] = []
      reify [] r = [r]
      
      table' = union 
              (reify (binary AssocLeft  <$> left) []) 
              (reify (binary AssocNone  <$> none) []) 
              (reify (binary AssocRight <$> right) [])
      
      binary assoc (v,nm) = (v,flip Infix assoc $ do
        reservedOp nm
        return $ \a b -> Spine nm [a , b])
        
  buildExpressionParser (table++table') tiper

pAtom :: Parser Spine
pAtom =  do reserved "_"
            nm <- getNextVar
            nm' <- getNextVar
            return $ infer nm atom $ infer nm' (var nm) $ var nm'
     <|> do r <- idVar
            return $ var r
     <|> do r <- identifier
            return $ var r
     <?> "atom"
  
pArg = pAtom <|> (do 
  braces $ do
    (nm,ty) <- named decVar
    return $ Spine "#tycon#" [Spine nm [ty]])
  
trm = do reservedOp "λ" <|> reservedOp "\\"
         (nm,tp) <- parens anonNamed <|> anonNamed
         reservedOp "."
         tp' <- tmpState nm $ trm
         return $ Abs nm tp tp' 
   <|> do t <- pAtom <|> parens trm
          tps <- many $ pArg <|> parens trm <|> parens tipe
          return $ rebuildSpine t tps
   <|> parens tipe
   <?> "term"
   
tiper :: Parser Type
tiper = trm
    <|> do (nm,tp) <- brackets anonNamed
           tp' <- tmpState nm tipe
           return $ forall nm tp tp'
    <|> do (nm,tp) <- braces anonNamed
           tp' <- tmpState nm tipe
           return $ imp_forall nm tp tp'
    <|> do (nm,tp) <- angles anonNamed
           tp' <- tmpState nm tipe
           return $ infer nm tp tp'
    <|> do reservedOp "∀" <|> reserved "forall"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ forall nm tp tp'
    <|> do reservedOp "∃" <|> reserved "exists"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ exists nm tp tp'
    <|> do reservedOp "?∀" <|> reserved "?forall"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ imp_forall nm tp tp'           
    <|> do reservedOp "??" <|> reserved "infer"
           (nm,tp) <- parens anonNamed <|> anonNamed
           reservedOp "."
           tp' <- tmpState nm tipe
           return $ infer nm tp tp'           
    <?> "type"


reservedOperators = ["->", "=>", "<=", "⇐", "⇒", "→", "<-", "←", 
                     "\\", "?\\", 
                     "λ","?λ", 
                     "∀", "?∀", 
                     "?", 
                     "??", "∃", ".", "=", 
                     ":", ";", "|"]
identStartOps = "_'-/"                     
                    
reservedNames = ["defn", "as", "query"    
                , "forall", "exists", "?forall"
                , "_" , "infer", "let"
                , "be", "infixl", "infixr", "infix"]

mydef :: P.GenLanguageDef String ParseState Identity
mydef = haskellDef
  { P.identStart = lower
  , P.identLetter = alphaNum <|> oneOf identStartOps
  , P.reservedNames = reservedNames
  , P.caseSensitive = True
  , P.reservedOpNames = reservedOperators
  , P.opStart = noneOf $ "# \n\t\r\f\v"++['a'..'z']++['A'..'Z']
  , P.opLetter = noneOf $ " \n\t\r\f\v"++['a'..'z']++['A'..'Z']
  }
P.TokenParser{..} = P.makeTokenParser mydef

getId :: Parser Char -> Parser String
getId start = P.identifier $ P.makeTokenParser mydef { P.identStart = start }
