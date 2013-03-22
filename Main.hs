
module Main where

import Options
import AST
import Choice
import HOU
import Parser
import System.Environment
import Data.Foldable as F (forM_)
import Data.List (partition)
import Data.Monoid
import Control.Monad (when)

import Data.IORef

import Control.Lens.Getter ((^.))
import Language.Preprocessor.Cpphs

-----------------------------------------------------------------------
-------------------------- MAIN ---------------------------------------
-----------------------------------------------------------------------
checkAndRun verbose decs = do
  
  when verbose $ do
    putStrLn "\nFILE: "
    forM_ decs $ \s -> putStrLn $ show s++"\n"

  when verbose $ putStrLn "\nTYPE CHECKING: "
  decs <- case runError $ typeCheckAll verbose decs of
    Left e -> error e
    Right e -> do when verbose $ putStrLn "Type checking success!"
                  return e
  let (defs,others)  = flip partition decs $ \x -> case x of
        Define {} -> True
        _ -> False
      
      sub = subst $ foldr (\a r -> r *** (predName a |-> subst r (predValue a))) mempty defs
      (predicates, targets) = flip partition others $ \x -> case x of
        Predicate {} -> True
        _ -> False
  
  when verbose $ do
    putStrLn "\nAXIOMS: "
    forM_ (defs++predicates) $ \s -> putStrLn $ show s++"\n"

  when verbose $ do
    putStrLn "\nTARGETS: "
    forM_ targets $ \s -> putStrLn $ show s++"\n"

  let predicates' = sub predicates
      targets' = sub targets
      
      axioms = toSimpleAxioms predicates'
  
  forM_ targets' $ \target -> do
    when verbose $ putStrLn $ "\nTARGET: \n"++show target
    case solver axioms $ predType target of
      Left e -> putStrLn $ "ERROR: "++e
      Right sub -> when verbose $ putStrLn $ "SOLVED WITH:\n"
                   ++concatMap (\(a,b) -> a++" => "++show b++"\n") sub


processFile :: Options -> IO ()
processFile options = do
  let fname = options ^. optFile
      
  writeIORef levelVar $ options ^. optVerbose
  
  file <- readFile fname
  
  file <- runCpphs 
          (defaultCpphsOptions{ 
              boolopts = defaultBoolOptions{ hashline = False 
                                           , lang = False
                                           , ansi = True
                                           , layout = True
                                           }
              }
          )
          fname file
  
  let mError = parseCaledon fname file 
  decs <- case mError of
    Left e -> error $ show e
    Right l -> return l
  checkAndRun (not $ options ^. optIO_Only) $ reduceDecsByName decs
          
main = do
  (options, files) <- compilerOpts =<< getArgs
  
  processFile $ options & case files of
    [] -> id
    [fname] -> optFile .~ fname
    _ -> error $ "Too many file arguments."++header