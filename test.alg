defn num  : atom
  is zero = num
   | succ = num -> num

defn List : atom -> atom
  is nil  = [A : atom] List A
   | cons = [A : atom] A -> List A -> List A

defn add   : num -> num -> num -> atom
  is add-z = [N : num] add zero N N
   | add-s = [N : num][M : num][R : num] add (succ N) M (succ R) <- add N M R

query sum-1 = add (succ (succ zero)) 'v (succ (succ (succ zero)))
query sum-2 = add (succ (succ zero)) (succ (succ (succ zero))) 'v

defn Term : atom
  is lam = (Term -> Term) -> Term
   | app = Term -> Term -> Term

defn red : Term -> Term -> atom
  is red-lam  = [V : Term][F : Term -> Term] red (app (lam F) V) (F V)
   | red-app1 = [V1 : Term][V1' : Term][V2 : Term] 
                red (app V1 V2) (app V1' V2) <- red V1 V1'
   | red-app2 = [V1 : Term][V2' : Term][V2 : Term] 
                red (app V1 V2) (app V1 V2') <- red V2 V2'

defn Monad : (atom -> atom) -> atom
  is ReturnBind = [M : atom -> atom] 
                  ([a : atom] a -> M a -> atom) 
               -> ([a : atom][b : atom] M a -> (a -> M b) -> M b -> atom) 
               -> Monad M

defn Maybe   : atom -> atom
  is Just    = [a : atom] a -> Maybe a
   | Nothing = [a : atom] Maybe a

defn MaybeReturn : [a : atom] a -> Maybe a -> atom 
  is justReturn = [a : atom][V : a] MaybeReturn a V (Just a V)

defn MaybeBind : [a : atom][b : atom] Maybe a -> (a -> Maybe b) -> Maybe b -> atom 
  is justBind = [a : atom][b : atom][v : a][f : a -> Maybe b] 
                MaybeBind a b (Just a v) f (f v)
   | nothingBind = [a : atom][b : atom][f : a -> Maybe b] 
                   MaybeBind a b (Nothing a) f (Nothing b)

defn MaybeMonad : Monad Maybe -> atom
  is maybeMonad = MaybeMonad (ReturnBind {Maybe} MaybeReturn MaybeBind)
