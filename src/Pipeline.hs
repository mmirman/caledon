module Src.Pipeline where

import Src.Elaborate
import Src.Reconstruction
import Src.HOU
import Src.AST
import Debug.Trace

infer (graph , constants) tm ty = do
  (tm    , constraints) <- typeConstraints constants tm ty
  (graph , recon)       <- unifyAll graph constants constraints
  return $ substReconstruct recon tm

pipe env@(graph , constants) name tm ty = do
  tm <- infer env tm ty
  trace (name++" : "++show tm) $ return ()
  
  