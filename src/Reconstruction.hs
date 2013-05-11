module Src.Reconstruction ( substReconstruct
                          , quantifyExistentials
                          ) where
import Names
import TopoSortAxioms
import Src.AST
import Src.Substitution
import Src.Context
import Data.Functor
import Src.FormulaSequence (Ctxt)
import qualified Data.Set as S
import qualified Data.Map as M

noType nm = error $ "no eta expansion necessary thus no type for "++nm

substReconstruct :: Reconstruction -> N -> N
substReconstruct recon t = foldr sub t $ filter (\(nm,(d,_)) -> inFrees (d,nm)) $ M.toList recon
  where sub (nm,(i,val)) = 
          substN' (val, Exi i nm $ noType nm)
        inFrees i = S.member (snd i) freeVars
        freeVars = M.keysSet $ freeVarsN t
        

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
                    
quantifyExistentials :: N -> N
quantifyExistentials n = case n' of
  Pat p -> Pat $ foldl (\b (a,ty) -> imp_forall (snd a) ty $ sub 0 a ty b) p genlst
  _ -> if null genlst 
              then n 
              else error $ "Can not quantify free existentials in a term: "++show n
  where n' = raiseAll n
        genmap :: M.Map Name (Int,Type)
        genmap = freeVarsMapN n'
        genlst = topoSort (\(nm,ty) -> (snd nm,M.keysSet $ freeVarsP ty)) $ map (\(a,(b,c)) -> ((b,a),c)) $ M.toList $ genmap
        
        sub i (depth,a) ty = substituteType (var i, ty, Exi depth a ty)