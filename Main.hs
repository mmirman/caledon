{-# LANGUAGE RecordWildCards #-}
module Main where

import Unifier 
import Choice
import Data.Foldable as F (msum, forM_)
import Data.Functor
import System.Environment
import Text.Parsec.String
import Text.Parsec
import Data.Monoid
import Control.Monad (unless)
import Text.Parsec.Language (haskellDef)
import Text.ParserCombinators.Parsec.Char
import Text.Parsec.Expr
import qualified Text.Parsec.Token as P
import qualified Data.Set as S
import Data.List (partition)

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
  let more =  do reserved "is"
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
    <?> "atom"

trm = parens trm 
   <|> do t <- atom
          tl <- many (atom <|> parens trm)
          return $ foldl App t tl
   <?> "term"

table = [ [binary "->" (:->:) AssocRight] ]
  where  binary  name fun assoc = Infix (reservedOp name >> return fun) assoc
         
namedTipe c = do nm <- identifier
                 reserved c
                 ty <- topTipe
                 return (nm, ty)
               
tmpState nm m = do
  s <- getState
  let b = S.member nm s
  putState $ S.insert nm s
  r <- m
  unless b $ modifyState (S.delete nm)
  return r

topTipe = buildExpressionParser table tipe

tipe =  parens topTipe
    <|> (Atom False <$> trm)
    <|> do (nm,tp) <- brackets $ namedTipe ":"
           tp' <- tmpState nm topTipe
           return $ Forall nm tp tp'
    <|> do (nm,tp) <- braces $ namedTipe ":"
           tp' <- tmpState nm topTipe
           return $ Exists nm tp tp'

    <?> "type"
           
P.TokenParser{..} = P.makeTokenParser $ haskellDef 
 { P.identStart = letter
 , P.identLetter = alphaNum <|> oneOf "_'-/"
 , P.reservedNames = ["defn", "is", "query", "=", ":", "|"]
 , P.caseSensitive = True
 , P.reservedOpNames = ["->"]
 }

-----------------------------------------------------------------------
-------------------------- MAIN ---------------------------------------
-----------------------------------------------------------------------
checkAndRun predicates targets = do
  putStrLn $ "AXIOMS: "
  forM_ predicates  $ \s -> putStrLn $ show s++"\n"
  
  putStrLn $ "\nTARGETS: "
  forM_ targets  $ \s -> putStrLn $ show s++"\n"
  
  putStrLn "\nTYPE CHECKING: "
  case runError $ typeCheckAll $ targets++predicates of
    Left e -> error e
    Right () -> putStrLn "Type checking success!"

  forM_ targets $ \target -> case solver (snd <$> concatMap predConstructors predicates) (predType target) of
    Left e -> putStrLn $ "ERROR: "++e
    Right sub -> putStrLn $ "\nTARGET: \n"++show target++"\n\nSOLVED WITH:\n"++concatMap (\(a,b) -> a++" => "++show b++"\n") sub

main = do
  [fname] <- getArgs
  file <- readFile fname
  let mError = runP decls mempty fname file
  decs   <- case mError of
    Left e -> error $ show e
    Right l -> return l
  uncurry checkAndRun $ flip partition decs $ \x -> case x of 
                                   Predicate _ _ _ -> False
                                   _ -> True
                                   
{-
 (OO)
  ##xxxxxxxxxxxxx------------------------
  ##xxxxxxxxxxxxx------------------------
  ##xxxxxxxxxxxxx------------------------
  ##xxxxxxxxxxxxx----AMERCA F**K YEAH ---
  ##xxxxxxxxxxxxx------------------------
  ##-------------------------------------
  ##-------------------------------------
  ##-------------------------------------
  ##-------------------------------------
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##
  ##  \o__
  ##   |
  ##  / \  .|.  /./ .  \.  .  \   
````````````````````````````````
:::::::;;;;;;;;;;;:;;;;;:;;:;;;;

-}

