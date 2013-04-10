{-# LANGUAGE
 RecordWildCards,
 TemplateHaskell,
 FlexibleContexts,
 IncoherentInstances,
 TypeSynonymInstances,
 FlexibleInstances,
 MultiParamTypeClasses
 #-}

module Parser (parseCaledon) where

import AST
import Substitution
import Control.Applicative (Applicative(..))
import Data.Functor
import Data.Functor.Identity
import Text.Parsec
import Control.Monad (unless)
import Control.Monad.State.Class
import Text.Parsec.Language (haskellDef)
import Text.Parsec.Expr 
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Text.Parsec.Token as P
import qualified Data.Set as S
import Debug.Trace
import qualified Data.Foldable as F

import Control.Lens 

-----------------------------------------------------------------------
-------------------------- PARSER -------------------------------------
-----------------------------------------------------------------------

data Fixity = FixLeft | FixRight | FixNone

data FixityTable = FixityTable { _fixityBinary :: [(Integer,String, Assoc)] 
                               , _fixityPrefix :: [(Integer, String, Assoc)]
                               , _fixityPostfix :: [(Integer, String, Assoc)]
                               , _opLambdas :: [String]
                               , _strLambdas :: [String]
                               , _binds :: [(String,String,String)]
                               }
                   
                   
data ParseState = ParseState { _currentVar :: Integer
                             , _currentSet :: S.Set Name
                             , _currentTable :: FixityTable 
                             , _currentOps :: [Name]
                             }
$(makeLenses ''FixityTable)                  
$(makeLenses ''ParseState)



-- | `parseCaledon` is the external interface
parseCaledon :: SourceName -> String -> Either ParseError [Decl]
parseCaledon = runP decls emptyState


emptyTable = FixityTable [] [] [] [] [] []
emptyState = (ParseState 0 mempty emptyTable [])

type Parser = ParsecT String ParseState Identity

instance MonadState ParseState Parser where
  get = getState
  put = putState


getNextVar :: Parser String
getNextVar = do
  v <- use currentVar
  currentVar %= (+1)
  return $ show v++"'"

decls :: Parser [Decl]
decls = do
  whiteSpace
  lst <- many (topLevel <?> "declaration")
  eof
  return $ catMaybes lst

topLevel = Nothing <$ fixityDef 
       <|> Just <$> query 
       <|> Just <$> defn 
       <* optional (many semi)
  
fixityDef = do
  reserved "fixity"
  infixDef <|> lamDef
                                                                    
lamDef = do
  reserved "lambda"
  opLam <|> strLam

opLam = addOpLam operator opLambdas
strLam = addOpLam identifier strLambdas

addOpLam ident lens = do
  op <- ident
  currentTable.lens %= (op:)
  
infixDef = do  
  setFixity <- (reserved "left" >> return (\b c -> over fixityBinary (c AssocLeft) b))
           <|> (reserved "none" >> return (\b c -> over fixityBinary (c AssocNone) b))
           <|> (reserved "right" >> return (\b c -> over fixityBinary (c AssocRight) b))
           <|> (reserved "pre" >> return (\b c -> over fixityPrefix (c undefined) b))
           <|> (reserved "post" >> return (\b c -> over fixityPostfix (c undefined) b))
  n <- integer
  op <- operator
  
  let modify assoc = insertBy (\(n,_,_) (m,_,_) -> compare n m) (n,op, assoc)
  
  currentTable %= flip setFixity modify
  currentOps %= (op:)
  

query :: Parser Decl
query = do
  reserved "query" 
  uncurry Query <$> named decPred

defn :: Parser Decl
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
                 return $ Predicate s nm ty lst
      none = do return $ Predicate s nm ty []
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
  s <- use currentSet
  let b = S.member nm s
  currentSet %= S.insert nm
  r <- m
  unless b $ currentSet %= S.delete nm
  return r




pChar = toNCCchar <$> charLiteral
pString = toNCCstring <$> stringLiteral


pTipe = do
  FixityTable bin prefix postfix opLams strLams binds <- use currentTable
  
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
                , regPostfix angles ["??"] ["infer"] infer
                , regPostfix brackets ["∀"] ["forall"] forall
                , regPostfix braces ["?∀"] ["?forall"] imp_forall
                ]++[ altPostfix [op] [] (\nm t s -> Spine op [t, Abs nm ty_hole s] ) | op <- opLams ]
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
        
      pOp = do operators <- use currentOps
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

      pTycon = braces $ uncurry tycon <$> named decVar
      
      myParens s m = (symbol "(" <?> ("("++s)) *> m <*  (symbol ")" <?> (s++")"))
      
  ptipe <?> "tipe"

reservedOperators = [ "->", "=>", "<=", "⇐", "⇒", "→", "<-", "←", 
                     "\\", "?\\", 
                     "λ","?λ", 
                     "∀", "?∀",
                     "?", 
                     "??", "=", 
                     ":", ";", "|"]
identRegOps = "_'-/"              
                    
reservedNames = ["defn", "as", "query", "unsound"
                , "forall", "?forall", "lambda", "?lambda"
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


