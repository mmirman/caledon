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

showTarget :: Predicate -> [(Name, Tm)] -> String
showTarget t s = "\nTARGET: \n" ++ show t ++ "\n\nSOLVED WITH:\n" ++ concatMap (\(a,b) -> a ++ " => " ++ show b ++ "\n") s

isPredicate :: Predicate -> Bool
isPredicate Predicate {} = True
isPredicate _            = False

allTypes :: Predicate -> [(Name, Tp)]
allTypes x = (predName x, predType x) : predConstructors x

typeCheck :: [Predicate] -> IO [Predicate]
typeCheck decs = case runError $ typeCheckAll decs of
    Left  e -> error e
    Right p -> putStrLn "Type checking success!" >> return p

solveTarget :: [Predicate] -> Predicate -> IO ()
solveTarget ps t = putStrLn $ case solver (first Cons <$> concatMap allTypes ps) $ predType t of
    Left  e -> "Error: " ++ e
    Right s -> showTarget t s

checkAndRun :: [Predicate] -> IO ()
checkAndRun decs = do

  putStrLn $ "FILE: \n" ++ showDecs decs

  putStrLn "\nTYPE CHECKING: "
  typedDecs <- typeCheck decs

  let (predicates, targets) = partition isPredicate typedDecs

  putStrLn $ "\nAXIOMS: \n"  ++ showDecs predicates
  putStrLn $ "\nTARGETS: \n" ++ showDecs targets

  mapM_ (solveTarget predicates) targets

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