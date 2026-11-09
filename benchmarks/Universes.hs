module Main where

import Universe
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import qualified Data.Map.Strict as M
import System.CPUTime (getCPUTime)
import Text.Printf (printf)

main :: IO ()
main = do
  putStrLn "constraints,shape,cpu_seconds,max_level"
  forM_ [1000,10000,100000] $ \n -> do
    let names = map show [0..n]
        chain = zipWith (:<:) names (drop 1 names)
        wide = ["root" :<: name | name <- drop 1 names]
    forM_ [("chain",chain),("fanout",wide)] $ \(shape,cs) -> do
      -- Force the input before timing; include full certificate construction.
      _ <- evaluate $ sum [length a + length b | a :<: b <- cs]
      start <- getCPUTime
      result <- evaluate $ force $ solveUniverses cs
      end <- getCPUTime
      case result of
        Nothing -> error "Satisfiable benchmark rejected"
        Just levels -> printf "%d,%s,%.6f,%d\n" (n :: Int) shape
          (fromIntegral (end-start) / 1e12 :: Double) (maximum $ M.elems levels)
