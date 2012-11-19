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

import Debug.Trace
-----------------------------------------------------------------------
-------------------------- PARSER -------------------------------------
-----------------------------------------------------------------------
decls = do
  whiteSpace
  lst <-many (query <|> defn <?> "not a thing")
  eof
  return lst

query = do 
  reserved "query" 
  (nm,ty) <- namedTipe "="
  semi
  return $ Query nm ty

defn =  do
  reserved "defn" 
  (nm,ty) <- namedTipe ":"
  let more =  do reserved "is"
                 lst <- flip sepBy1 (reserved "|") $ namedTipe "="
                 semi
                 return $ Predicate nm ty lst
      none = do semi
                return $ Predicate nm ty []
  none <|> more             
  

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
  uncurry checkAndRun $ break (\x -> case x of 
                                   Predicate _ _ _ -> False
                                   _ -> True) decs
-----------------------------------------------------------------------
-------------------------- TEST ---------------------------------------
-----------------------------------------------------------------------  
test = do  
  let var = Var
      cons = Cons
      
      tp = Atom False
      
      atom = tp $ Cons "atom"
      nat = tp $ Cons "nat"
      
      addRes a b c = tp $ cons "add" .+. a .+. b .+. c
      zero = cons "zero"
      succ a = cons "succ" .+. a
      
      infixr 5 $
      f $ i = f i
      infixr 4 =:
      (=:) a b = (a,b)
      infixl 3 |:
      (|:) foo a = foo a []
      infixl 2 <|
      foo <| a = foo { predConstructors = a:predConstructors foo }
      
      vr v = tp $ var v      
      lst v = tp $ cons "list" .+. var v

      predicates = [ Predicate "nat" |: atom
                     <| "zero" =: nat
                     <| "succ" =: nat :->: nat
                   , Predicate "add" |: nat :->: nat :->: nat :->: atom
                     <| "add-z" =: Forall "result" nat $ addRes zero (var "result") (var "result")
                     <| "add-s" =: Forall "m" nat $ Forall "n" nat $ Forall "res" nat $ addRes (var "n") (var "m") (var "res") :->: addRes (succ $ var "n") (var "m") (succ $ var "res")
                   , Predicate "list" |: atom :->: atom
                     <| "nil" =: Forall "a" atom $ lst "a"
                     <| "cons" =: Forall "a" atom $ vr "a" :->: lst "a" :->: lst "a"
                   , let cat v a b c = tp $ cons "concat" .+. var v .+. a .+. b .+. c
                         nil v = cons "nil" .+. var v
                         con v a b = cons "cons" .+. var v .+. a .+. b
                     in 
                     Predicate "concat" |: Forall "a" atom $ lst "a" :->: lst "a" :->: lst "a" :->: atom
                     <| "concat-nil" =: Forall "a" atom $ Forall "N" (lst "a") $ cat "a" (nil "a") (var "N") (var "N")
                     <| "concat-suc" =: Forall "a" atom $ Forall "V" (vr "a") $ Forall "N" (lst "a") $ Forall "M" (lst "a") $ Forall "R" (lst "a") $ 
                          cat "a" (var "N") (var "M") (var "R") 
                          :->: cat "a" (con "a" (var "V") (var "N")) (var "M") (con "a" (var "V") (var "R"))
                   ]
      
      target = Query "result" $ addRes (succ $ succ $ zero) (var "what") (succ $ succ $ succ $ zero) 

  checkAndRun predicates [target]


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

