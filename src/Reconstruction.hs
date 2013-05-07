module Src.Reconstruction ( substReconstruct
                          ) where

import Src.AST
import Src.Substitution
import Src.Context
import Src.FormulaSequence (Ctxt)
import qualified Data.Set as S
import qualified Data.Map as M

noType nm = error $ "no eta expansion necessary thus no type for "++nm

substReconstruct :: Reconstruction -> Type -> Type
substReconstruct recon t = foldr sub t $ filter (inFrees . fst) $ M.toList recon
  where sub (nm,(i,val)) = 
          substN False (emptyCon constants :: Ctxt) (val, noType nm, Exi i nm $ noType nm)
        inFrees i = S.member i freeVars
        freeVars = freeVarsN t