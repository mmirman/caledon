module Paths_caledon (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch


version :: Version
version = Version {versionBranch = [0,0,0,0], versionTags = []}
bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/Users/devin/bin"
libdir     = "/Users/devin/lib"
datadir    = "/Users/devin/share"
libexecdir = "/Users/devin/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = catchIO (getEnv "caledon_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "caledon_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "caledon_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "caledon_libexecdir") (\_ -> return libexecdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
