{-# LANGUAGE 
 TemplateHaskell,
 FlexibleContexts
 #-}
module Options where
import Data.List

import Data.Maybe
import Control.Lens (makeLenses, (.~))
import System.Console.GetOpt

data Options = Options 
               { _optIO_Only :: Bool
               , _optVerbose :: Int
               , _optFile :: String
               , _optHelp :: Maybe String
               }
               
$(makeLenses ''Options)     

defaultOptions = Options 
               { _optIO_Only  = False
               , _optVerbose  = 0
               , _optFile     = ""
               , _optHelp     = Nothing
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
  , Option ['h'] ["help"]
    (OptArg ((optHelp .~) . Just . fromMaybe helpMsg . fmap getMsg) "OPTION")
    "display this help message"
  ]

helpMessage = "Usage is \"caledon [--io-only] file.ncc\""

compilerOpts :: [String] -> IO (Options,[String])
compilerOpts argv = 
  case getOpt Permute options argv of
    (o,n,[] ) -> return (foldl (flip id) defaultOptions o, n)
    (_,_,errs) -> ioError $ userError $ concat errs ++ helpMsg

helpMsg = usageInfo header options
getMsg option = usageInfo header $ maybeToList 
                $ find (\(Option s l _ _) -> elem option $ concat $ 
                                         [[['-',i],[i]] | i <- s ] 
                                       ++[["--"++i,i]   | i <- l ] 
                       ) options
  
header = "Usage: caledon [OPTIONS] file.ncc" 