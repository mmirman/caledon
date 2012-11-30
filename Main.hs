{-# LANGUAGE RecordWildCards #-}
module Main where

import AST
import Unifier 
import Choice
import Parser
import System.Environment
import Data.Foldable as F (msum, forM_)
import Data.Functor
import Data.List (partition)
import Text.Parsec
import Data.Monoid

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

  let allTypes c = (predName c, predType c):predConstructors c
  forM_ targets $ \target -> case solver (concatMap allTypes predicates) (predType target) of
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
                                   Predicate _ _ _ -> True
                                   _ -> False
