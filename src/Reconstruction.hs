module Src.Reconstruction ( substReconstruct
                          , raiseAll
                          , quantifyExistentials
                          ) where

import TopoSortAxioms
import Src.AST
import Src.Substitution
import Src.Context
import Src.FormulaSequence (Ctxt)
import qualified Data.Set as S
import qualified Data.Map as M

noType nm = error $ "no eta expansion necessary thus no type for "++nm

substReconstruct :: Reconstruction -> N -> N
substReconstruct recon t = foldr sub t $ filter (inFrees . fst) $ M.toList recon
  where sub (nm,(i,val)) = 
          substN False (emptyCon constants :: Ctxt) (val, noType nm, Exi i nm $ noType nm)
        inFrees i = S.member i freeVars
        freeVars = freeVarsN t
        

raiseAll :: N -> N
raiseAll = ran []
  where ran lst n = case n of
          Pat p -> Pat $ rap lst p
          Abs ty a -> Abs (rap lst ty) (ran (ty:lst) a) 
        rap lst p = case p of
          a :+: b -> rap lst a :+: ran lst b
          Var v -> case v of
            Con c -> Var $ Con c
            DeBr i -> Var $ DeBr i
            Exi 0 nm ty -> Var $ Exi 0 nm ty
            Exi i nm ty -> foldl (:+:) exi' (reverse args)
              where fromBot = length lst - i - 1
                    (args,types) = unzip $ drop fromBot $ zip (map (Pat . Var . DeBr) [0..]) lst
                    ty' = foldr forall (rap lst ty) (reverse types)
                    exi' = Var $ Exi 0 nm ty'
                    
quantifyExistentials :: N -> Type
quantifyExistentials n = foldr (\(i,(a,ty)) b -> imp_forall a ty $ sub i a ty b) (fromType n') gens
  where n' = raiseAll n
        genmap = freeVarsMapN n'
        genlst = topoSort (\(nm,ty) -> (nm,freeVarsP ty)) $ M.toList $ genmap
        
        gens = uncurry zip $ (\(a,b) -> (reverse a, b)) $ unzip $ (zip [0..] genlst)
        
        sub i a ty = substituteType (var i, ty, Exi i a ty)