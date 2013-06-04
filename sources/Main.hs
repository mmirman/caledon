
module Main where

import Options
import AST
import Substitution
import Src.Tracing
import Choice
import HOU
import qualified Src.Pipeline as Src
import Parser
import System.Environment
import Data.Foldable as F (forM_)
import Data.List (partition)
import Data.Monoid
import Control.Monad (when)

import Data.IORef

import Control.Lens ((^.), (.~), (&))
import Language.Preprocessor.Cpphs

-----------------------------------------------------------------------
-------------------------- MAIN ---------------------------------------
-----------------------------------------------------------------------
checkAndRun verbose decs = do
  
  when verbose $ do
    putStrLn "\nFILE: "
    forM_ decs $ \s -> putStrLn $ show s++"\n"

  when verbose $ putStrLn "\nCOMPILING: "
  decs <- case runError $ Src.typeCheckAll verbose decs of
    Left e -> error e
    Right e -> do when verbose $ putStrLn "DONE: compilation success!\n"
                  return e
                  
  let (defs,others)  = flip partition decs $ \x -> case x of
        Define {} -> True
        _ -> False
      
      sub = subst $ foldr (\a r -> r *** ((a^.declName) |-> subst r (a^.declValue))) mempty defs
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
    case solver axioms $ target ^. declType of
      Left e -> putStrLn $ "ERROR: "++e
      Right sub -> when verbose $ putStrLn $ "SOLVED WITH:\n"
                   ++concatMap (\(a,b) -> a++" => "++show b++"\n") sub


processFile :: Options -> IO ()
processFile options | options ^. optHelp /= Nothing = case options ^. optHelp of
  Just s -> putStrLn s
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
  writeIORef levelVar 0
  
  (options, files) <- compilerOpts =<< getArgs
  
  processFile $ options & case files of
    [] -> id
    [fname] -> optFile .~ fname
    _ -> error $ "Too many file arguments."++header