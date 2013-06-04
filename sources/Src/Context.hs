module Src.Context where

import Src.AST

class Show a => Context a where
  getTy :: a -> Variable -> Type
  getVal:: a -> Variable -> Term
  putTy :: a -> Type -> a
  height :: a -> Int
  emptyCon :: Constants -> a
  
  getTypes :: a -> (Constants, [Type])

emptyErr = error "\nContext () not for actual use" 
instance Context () where  
  getTy = emptyErr
  getVal = emptyErr
  height = emptyErr
  emptyCon = emptyErr
  getTypes = emptyErr
  putTy = emptyErr
  
class (Show a, Context a) => Environment a where
  putLeft :: a -> Form  -> a
  putRight :: Form -> a -> a
  
  rebuild :: a -> Form -> Form
  
  upI :: Int -> a -> Form -> Maybe (a,Form)
  
  isDone :: a -> Bool
  
  nextUp :: (a,Form) -> (a,Form)
  viewLeft :: (a,Form) -> Maybe (a,Form)
  viewRight :: (a,Form) -> Maybe (a,Form)

reset a Done | isDone a = (a,Done)
reset a Done = uncurry reset $ nextUp(a,Done)
reset a f = (a,f)