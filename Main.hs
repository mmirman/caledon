module Main where

import AST
import Choice
import Solver
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
checkAndRun decs = do
  
  putStrLn "\nTYPE CHECKING: "
  decs <- case runError $ typeCheckAll $ decs of
    Left e -> error e
    Right e -> do putStrLn "Type checking success!" >> return e
  let (predicates, targets) = flip partition decs $ \x -> case x of 
        Predicate _ _ _ -> True
        _ -> False

  
  putStrLn $ "\nAXIOMS: "
  forM_ predicates  $ \s -> putStrLn $ show s++"\n"
  
  putStrLn $ "\nTARGETS: "
  forM_ targets  $ \s -> putStrLn $ show s++"\n"

  let allTypes c = (predName c, predType c):predConstructors c
  forM_ targets $ \target -> 
    case solver (concatMap allTypes predicates) $ predType target of
      Left e -> putStrLn $ "ERROR: "++e
      Right sub -> putStrLn $ 
                   "\nTARGET: \n"++show target
                   ++"\n\nSOLVED WITH:\n"
                   ++concatMap (\(a,b) -> a++" => "++show b++"\n") sub

main = do
  [fname] <- getArgs
  file <- readFile fname
  let mError = runP decls (ParseState 0 mempty) fname file
  decs   <- case mError of
    Left e -> error $ show e
    Right l -> return l
  checkAndRun decs 