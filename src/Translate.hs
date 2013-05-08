module Src.Translate ( consToForm
                     , toSpine
                     , fromSpine
                     ) where

import Names
import qualified AST as A
import qualified Src.AST as B
import qualified Src.Reconstruction as B
import qualified Src.Context as B
import qualified Data.Map as M
import Data.Functor
import Data.Monoid

import Data.IORef
import System.IO.Unsafe
  
------------------------------
--- conversion to debruijn ---
------------------------------
data Stack = Stack { stackLen :: Int
                   , stackMap :: M.Map Name Int
                   , stackExistsMap :: M.Map Name (Int,B.Type)
                   }
             
putName :: Stack -> Name -> Stack             
putName (Stack sl sm se) n = Stack (sl + 1) (M.insert n sl sm) (M.delete n se)

getIndex :: Stack -> Name -> Maybe Int
getIndex (Stack sl sm se) n = (sl -) <$> M.lookup n sm

putExists :: Stack -> Name -> B.Type -> Stack
putExists (Stack sl sm se) n ty = Stack sl (M.delete n sm) (M.insert n (sl,ty) se) 

getExists :: Stack -> Name -> Maybe (Int,B.Type)
getExists (Stack sl sm se) n = do
  ~(i,t) <- M.lookup n se
  return $ (i, B.liftV (sl - i) t)
  
newStack :: Stack
newStack = Stack 0 mempty mempty

isGen [] = False
isGen (c:s) = elem c ['A'..'Z']
  


s2n :: Stack -> A.Spine -> B.N 
s2n stk s = case s of 
  A.Spine n l -> B.Pat $ foldl (B.:+:) np $ s2n stk <$> l
    where np = B.Var $ case getIndex stk n of
            Nothing -> case getExists stk n of
              Just (i,ty) -> B.Exi i n ty
              Nothing -> case isGen n of 
                True -> B.Exi 0 n $ B.Var $ B.Exi 0 ('@':n) B.tipe
                False -> B.Con n
            Just i  -> B.DeBr i
  A.Abs n ty s -> B.Abs (B.fromType $ s2n stk ty) $ s2n (putName stk n) s

scons2form :: Stack -> A.SCons -> B.Form
scons2form stk c = case c of
  t A.:@: s -> s2n stk t B.:@: B.fromType (s2n stk s)
  t A.:=: s -> s2n stk t B.:=: s2n stk s
  
cons2form :: Stack -> A.Constraint -> B.Form
cons2form stk c = case c of
  A.SCons [] -> B.Done -- shouldn't exist!
  A.SCons l -> foldr1 (B.:&:) (scons2form stk <$> l)
  a A.:&: b -> cons2form stk a B.:&: cons2form stk b
  A.Bind A.Forall n ty c -> B.Bind (B.fromType $ s2n stk ty) 
                            $ cons2form (putName stk n) c
  A.Bind A.Exists n ty c -> cons2form (putExists stk n ty') c
    where ty' = B.fromType $ s2n stk ty

---------------------------
--- conversion to names ---
---------------------------
data UnStack = UnStack { unStackLen :: Int
                       , unStack :: [Name]
                       }

newUnstack = UnStack 0 []

nToSpine :: B.N -> A.Spine
nToSpine = n2s newUnstack

n2s :: UnStack -> B.N -> A.Spine
n2s stk@(UnStack i lst) n = case n of
  B.Abs ty n -> A.Abs next (n2s stk $ B.Pat ty) $ n2s (UnStack (i+1) $ next:lst) n
    where next = '@':show i
  B.Pat p -> A.Spine nm $ reverse l
    where ~(nm,l) = p2s stk p
  
p2s :: UnStack -> B.P -> (Name,[A.Spine])
p2s stk@(UnStack i lst) p = case p of
  B.Var v -> case v of
    B.DeBr i -> (lst !! i,[])
    B.Exi i n ty -> (n,[])
    B.Con n -> (n,[])
  p B.:+: n -> (nm,n2s stk n:l)
    where ~(nm,l) = (p2s stk p)


--------------------------
--- The reconstruction ---
--------------------------
consToForm :: (A.Spine,A.Constraint) -> (B.Term,B.Form)
consToForm (a,b)= (s2n newStack a, cons2form newStack b) 

fromSpine = s2n newStack

toSpine :: B.Term -> A.Spine
toSpine = nToSpine