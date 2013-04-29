module Src.Context where

import Src.AST

class Context a where
  getTy :: a -> Variable -> Type
  putTy :: a -> Type -> a
  height :: a -> Int
  emptyCon :: Constants -> a
  
  getTypes :: a -> (Constants, [Type])
  
class Context a => Environment a where
  putLeft :: a -> Form  -> a
  putRight :: Form -> a -> a
  
  rebuild :: a -> Form -> Form
  
  upI :: Int -> a -> Form -> Maybe (a,Form)
  


