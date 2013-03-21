{-# LANGUAGE 
 TemplateHaskell,
 FlexibleContexts
 #-}
module Options where

import Data.Maybe
import Control.Lens
import System.Console.GetOpt

data Options = Options 
               { _optIO_Only :: Bool
               , _optVerbose :: Int
               , _optFile :: String
               } 
$(makeLenses ''Options)     

defaultOptions = Options 
               { _optIO_Only = False
               , _optVerbose  = 0
               , _optFile   = ""
               }


options :: [OptDescr (Options -> Options)]
options = 
  [ Option ['i'] ["io-only"]
    (NoArg $ optIO_Only .~ True)
    "don't print out typechecking info"
  , Option ['v'] ["verbosity"]
    (OptArg ((optVerbose .~) . fromMaybe 0 . fmap read) "VERBOSITY")
    "a number describing how much debugging information to print"
  , Option ['f'] ["file", "infile", "input"]
    (ReqArg (optFile .~) "INFILE")
    "a number describing how much debugging information to print"
  ]

helpMessage = "Usage is \"caledon [--io-only] file.ncc\""

arg_lst = [ ["--io-only", "-i"]
          , ["--verbosity", "-V"]
          , ["--help", "-h"]
          , ["--file", "-f"]
          ]
  
compilerOpts :: [String] -> IO (Options,[String])
compilerOpts argv = 
  case getOpt Permute options argv of
    (o,n,[] ) -> return (foldl (flip id) defaultOptions o, n)
    (_,_,errs) -> ioError $ userError $ concat errs ++ usageInfo header options

header = "Usage: caledon [OPTIONS] file.ncc"