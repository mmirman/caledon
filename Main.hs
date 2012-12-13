module Main where

import AST
import Choice
import Solver
import Parser

import System.Environment
import Data.Functor
import Data.Foldable as F (forM_)
import Data.List (partition, concatMap)
import Control.Arrow(first)
import Text.Parsec hiding (parse)
import Data.Monoid

-----------------------------------------------------------------------
-------------------------- MAIN ---------------------------------------
-----------------------------------------------------------------------

showDecs :: [Predicate] -> String
showDecs []   = []
showDecs decs = init $ init $ concatMap (\s -> show s ++ "\n\n") decs

typeCheck :: [Predicate] -> IO [Predicate]
typeCheck decs = do
    case runError $ typeCheckAll decs of
        Left e -> error e
        Right e -> putStrLn "Type checking success!" >> return e

isPredicate :: Predicate -> Bool
isPredicate Predicate {} = True
isPredicate _            = False

checkAndRun :: [Predicate] -> IO ()
checkAndRun decs = do
  putStrLn $ "FILE: \n" ++ showDecs decs

  putStrLn "\nTYPE CHECKING: "
  typedDecs <- typeCheck decs

  let (predicates, targets) = flip partition typedDecs isPredicate

  putStrLn $ "\nAXIOMS: \n" ++ showDecs predicates
  putStrLn $ "\nTARGETS: \n" ++ showDecs targets

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