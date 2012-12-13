module Main where

import AST
import Choice
import Solver
import Parser

import System.Environment
import Data.Functor
import Data.Foldable as F (forM_)
import Data.List (partition)
import Control.Arrow(first)
import Text.Parsec hiding (parse)
import Data.Monoid

-----------------------------------------------------------------------
-------------------------- MAIN ---------------------------------------
-----------------------------------------------------------------------
checkAndRun :: [Predicate] -> IO ()
checkAndRun decs = do

  putStrLn "\nFILE: "
  forM_ decs  $ \s -> putStrLn $ show s++"\n"

  putStrLn "\nTYPE CHECKING: "
  decs <- case runError $ typeCheckAll decs of
    Left e -> error e
    Right e -> putStrLn "Type checking success!" >> return e
  let (predicates, targets) = flip partition decs $ \x -> case x of
        Predicate{} -> True
        _           -> False


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

parseFile :: String -> IO (Either ParseError [Predicate])
parseFile fname = readFile fname >>= \file -> return $ runP decls (ParseState 0 mempty) fname file

main = do
  fnames <- getArgs
  case fnames of
    []      -> putStrLn "No file specified." --REPL Here
    [fname] -> do mDecls <- parseFile fname  --Parser
                  case mDecls of
                    Left e -> putStrLn "Parse Error:\n" >> print e
                    Right l -> checkAndRun l