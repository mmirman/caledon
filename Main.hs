module Main where

import AST
import Choice
import Solver
import Parser
import System.Environment
import Data.Functor
import Data.Foldable as F (forM_)
import Data.List (partition)
import Text.Parsec
import Data.Monoid
import Control.Arrow (first)

-----------------------------------------------------------------------
-------------------------- MAIN ---------------------------------------
-----------------------------------------------------------------------
checkAndRun decs = do

  putStrLn "\nFILE: "
  forM_ decs $ \s -> putStrLn $ show s++"\n"

  putStrLn "\nTYPE CHECKING: "
  decs <- case runError $ typeCheckAll decs of
    Left e -> error e
    Right e -> putStrLn "Type checking success!" >> return e
  let (predicates, targets) = flip partition decs $ \x -> case x of
        Predicate {} -> True
        _ -> False

  putStrLn "\nAXIOMS: "
  forM_ predicates $ \s -> putStrLn $ show s++"\n"

  putStrLn "\nTARGETS: "
  forM_ targets $ \s -> putStrLn $ show s++"\n"

  let allTypes c = (predName c, predType c):predConstructors c
  forM_ targets $ \target ->
    case solver (first Cons <$> concatMap allTypes predicates) $ predType target of
      Left e -> putStrLn $ "ERROR: "++e
      Right sub -> putStrLn $
                   "\nTARGET: \n"++show target
                   ++"\n\nSOLVED WITH:\n"
                   ++concatMap (\(a,b) -> a++" => "++show b++"\n") sub

main = do
  fnames <- getArgs
  case fnames of
    [] -> putStrLn "No file specified. Usage is \"caledon file.ncc\""
    [fname] -> do
      file <- readFile fname
      let mError = runP decls (ParseState 0 mempty) fname file
      decs <- case mError of
        Left e -> error $ show e
        Right l -> return l
      checkAndRun decs
    _ -> putStrLn "Unrecognized arguments. Usage is \"caledon file.ncc\""