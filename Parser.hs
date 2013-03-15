{-# LANGUAGE
 RecordWildCards
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
import Data.Monoid
import qualified Text.Parsec.Token as P
import qualified Data.Set as S
import Debug.Trace
import qualified Data.Foldable as F

-----------------------------------------------------------------------
-------------------------- PARSER -------------------------------------
-----------------------------------------------------------------------


data ParseState = ParseState { currentVar :: Integer
                             , currentSet :: S.Set Name
                             , currentTable :: FixityTable 
                             , currentOps :: [Name]
                             }

data Fixity = FixLeft | FixRight | FixNone

data FixityTable = FixityTable { fixityBinary :: [(Integer,String, Assoc)] 
                               , fixityPrefix :: [(Integer, String, Assoc)]
                               , fixityPostfix :: [(Integer, String, Assoc)]
                               , opLambdas :: [String]
                               , strLambdas :: [String]
                               , binds :: [(String,String,String)]
                               }

emptyTable = FixityTable [] [] [] [] [] []
emptyState = (ParseState 0 mempty emptyTable [])

type Parser = ParsecT String ParseState Identity

modifySet :: (S.Set Name -> S.Set Name) -> ParseState -> ParseState
modifySet f s = s { currentSet = f $ currentSet s }

modifyVar :: (Integer -> Integer) -> ParseState -> ParseState
modifyVar f s = s { currentVar = f $ currentVar s }

getNextVar :: Parser String
getNextVar = do
  v <- currentVar <$> getState
  modifyState $ modifyVar (+1)
  return $ show v++"'"

decls :: Parser [Predicate]
decls = do
  whiteSpace
  lst <- many (topLevel <?> "declaration")
  eof
  return lst

topLevel = fixityDef <|> query <|> defn

fixityDef = do 
  reserved "fixity"
  infixDef <|> lamDef
  topLevel
                                                                    
lamDef = do
  reserved "lambda"
  opLam <|> strLam

opLam = do  
  op <- operator
  modifyState $ \b -> b { currentTable = let ct = currentTable b in ct { opLambdas = op:opLambdas ct} }
                                                                    
strLam = do
  op <- identifier
  modifyState $ \b -> b { currentTable = let ct = currentTable b in ct { strLambdas = op:strLambdas ct} }
                                                                    
infixDef = do  
  -- I wish template haskell worked with record wild cards!
  (setFixity) <- (reserved "left" >> return (\b c -> b { fixityBinary = c AssocLeft $ fixityBinary b} )) 
             <|> (reserved "none" >> return (\b c -> b { fixityBinary = c AssocNone $ fixityBinary b} )) 
             <|> (reserved "right" >> return (\b c -> b { fixityBinary = c AssocRight $ fixityBinary b} )) 
             <|> (reserved "pre" >> return (\b c -> b { fixityPrefix = c undefined $ fixityPrefix b}))
             <|> (reserved "post" >> return (\b c -> b { fixityPostfix = c undefined $ fixityPostfix b}))
  n <- integer
  op <- operator -- <|> identifier
  
  let modify assoc = insertBy (\(n,_,_) (m,_,_) -> compare n m) (n,op, assoc)
  modifyState $ \b -> b { currentTable = setFixity (currentTable b) modify
                        , currentOps = op:currentOps b}
  

query :: Parser Predicate
query = do
  reserved "query"
  (nm,ty) <- named decPred
  optional semi
  return $ Query nm ty

defn :: Parser Predicate
defn = sound <|> unsound
  
sound = do
  reserved "defn"
  vsn True

unsound = do
  reserved "unsound" 
  vsn False
 
  
  
vsn s = do    
  (nm,ty) <- named decTipe
  let more =  do lst <- many1 $ do
                   seqi <- (reservedOp "|"  >> return False) 
                      <|> (reservedOp ">|" >> return True)
                   (nm,t) <- named decPred
                   return (seqi,(nm,t))
                        
                 optional semi
                 return $ Predicate s nm ty lst
      none = do optional semi
                return $ Predicate s nm ty []
      letbe = do reserved "as"
                 val <- pTipe
                 return $ Define s nm val ty
  letbe <|> more <|> none <?> "definition"




decTipe :: (Parser String, String)
decTipe = (operator <|> getId lower, ":")

decPred :: (Parser String, String)
decPred = (operator <|> getId lower, "=")

idVar :: Parser String
idVar = getId $ upper

decVar :: (Parser String, String)
decVar = (idVar <|> getId lower, "=")

decAnon :: (Parser String, String)
decAnon = (getId $ letter , ":")

named :: (Parser a, String) -> Parser (a, Type)
named (ident, sep) = do
  nm <- ident
  reservedOp sep
  ty <- pTipe
  return (nm, ty)

tmpState :: String -> Parser a -> Parser a
tmpState nm m = do
  s <- currentSet <$> getState
  let b = S.member nm s
  modifyState $ modifySet (S.insert nm)
  r <- m
  unless b $ modifyState $ modifySet $ S.delete nm
  return r




pChar = toNCCchar <$> charLiteral
pString = toNCCstring <$> stringLiteral


pTipe = do
  FixityTable bin prefix postfix opLams strLams binds <- currentTable <$> getState 
  
  let getSnd [] = []
      getSnd (a:l) = l
      getFst (a:l) = a
      getFst [] = []
                  
      union l | all null l = []
      union lst = concatMap getFst lst:union (getSnd <$> lst)
      
      reify ((a,op):(a',op'):l) r | a == a' = reify ((a',op'):l) (op:r)
      reify ((a,op):l) r = (op:r):reify l []
      reify [] [] = []
      reify [] r = [r]
      
      anonNamed = do
        let (ident,sep) = decAnon
        nml <- many ident
        ty <- optionMaybe $ reservedOp sep >> ptipe
        return (nml,fromMaybe ty_hole ty)

      binary fun assoc name = flip Infix assoc $ do 
        name
        fun <$> getNextVar
        
      altPostfix = prefixGen id
      regPostfix bind = prefixGen (bind anonNamed <|>)
        
      prefixGen bind opsl nms out = Prefix $ do
        (nml,tp) <- bind $ between 
                   (choice $ (reserved <$> nms)++(reservedOp <$> opsl))
                   (symbol ".")  
                   (parens anonNamed <|> anonNamed)
        return $ \input -> foldr (flip out tp) input nml
      
      table = [ [ altPostfix ["λ", "\\"] ["lambda"] Abs
                , altPostfix ["?λ", "?\\"] ["?lambda"] imp_abs
                , altPostfix ["∃"] ["exists"] exists
                , regPostfix angles ["??"] ["infer"] infer
                , regPostfix brackets ["∀"] ["forall"] forall
                , regPostfix braces ["?∀"] ["?forall"] imp_forall
                ]++[ altPostfix [op] [] (\nm t s -> Spine op [t,Abs nm ty_hole s] ) | op <- opLams ]
                ++[ altPostfix [] [op] (\nm t s -> Spine op [t,Abs nm ty_hole s] ) | op <- strLams ]
              , [ binary (forall) AssocRight $ reservedOp "->" <|> reservedOp "→" 
                , binary (const (~~>)) AssocRight $ reservedOp "=>" <|> reservedOp "⇒"
                ]
              , [ binary (flip . forall) AssocLeft $ reservedOp "<-" <|> reservedOp "←"
                , binary (flip . const (~~>)) AssocLeft $ reservedOp "<=" <|> reservedOp "⇐" 
                ]
              , [ binary (const ascribe) AssocNone $ reservedOp ":"
                ] 

                
              ]
             ++union [ reify (binaryOther <$> bin) [] 
                     , reify (unary Prefix <$> prefix) []
                     , reify (unary Postfix <$> postfix) []
                     ]
      
      binaryOther (v,nm, assoc) = (v,flip Infix assoc $ do
        reservedOp nm
        return $ \a b -> Spine nm [a , b])

      unary fix (v,nm,_) = (v,fix $ do
        reservedOp nm
        return $ \a -> Spine nm [a])

      ptipe = buildExpressionParser (reverse $ table) terminal
      -- now terms must be parsed in pattern normal form
      
      terminal = try trm <|> (myParens "terminal" ptipe) <|> ptipe <?> "terminal"
      
      trm =  do t <- pHead
                tps <- many pArg
                return $ rebuildSpine t tps
         <?> "term"

      
      pHead = pParens pAt (pOp <|> ptipe <|> pAsc) "head"
      pArg  = pParens (pAt <|> pTycon) (pOp <|> ptipe) "argument"
      
      pParens anyAmount atLeast1 nm = anyAmount <|> pothers <?> nm
        where others = atLeast1 <|> anyAmount <|> pothers <?> nm
              pothers = myParens nm others

      pAsc = do
        v <- trm
        let asc = do
              reservedOp ":"
              t <- ptipe 
              return $ ascribe v t
        (asc <|> return v <?> "function") 
        
      pOp = do operators <- currentOps <$> getState 
               choice $ flip map operators $ \nm -> do reserved nm 
                                                       return $ var nm
         <?> "operator"      
         
      pAt =  do reserved "_"
                return $ ty_hole
         <|> do r <- idVar
                return $ var r
         <|> do r <- identifier
                return $ var r
         <|> pChar
         <|> pString
         <?> "atom"

      pTycon = braces $ do
        (nm,ty) <- named decVar
        return $ tycon nm ty
      
      myParens s m = between (symbol "(" <?> ("("++s)) (symbol ")" <?> (s++")")) m
      
  ptipe <?> "tipe"

reservedOperators = [ "->", "=>", "<=", "⇐", "⇒", "→", "<-", "←", 
                     "\\", "?\\", 
                     "λ","?λ", 
                     "∀", "?∀",
                     "?", 
                     "??", "∃", "=", 
                     ":", ";", "|"]
identRegOps = "_'-/"              
                    
reservedNames = ["defn", "as", "query", "unsound"
                , "forall", "exists", "?forall", "lambda", "?lambda"
                , "_" , "infer", "fixity"]

mydef :: P.GenLanguageDef String ParseState Identity
mydef = haskellDef
  { P.identStart = oneOf $ "_"++['a'..'z']
  , P.identLetter = alphaNum <|> oneOf identRegOps
  , P.reservedNames = reservedNames
  , P.caseSensitive = True
  , P.reservedOpNames = reservedOperators
  , P.opStart = noneOf $ "# \n\t\r\f\v"++['a'..'z']++['A'..'Z']
  , P.opLetter = noneOf $ " \n\t\r\f\v"++['a'..'z']++['A'..'Z']
  }
P.TokenParser{..} = P.makeTokenParser mydef

getId :: Parser Char -> Parser String
getId start = P.identifier $ P.makeTokenParser mydef { P.identStart = start }
