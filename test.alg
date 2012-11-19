defn num  : atom
  is zero = num
   | succ = num -> num;

defn List : atom -> atom
  is nil  = [A : atom] List A
   | cons = [A : atom] A -> List A -> List A;

defn add   : num -> num -> num -> atom
  is add-z = [N : num] add zero N N
   | add-s = [N : num][M : num][R : num] add N M R -> add (succ N) M (succ R);

defn Term : atom
  is lam = (Term -> Term) -> Term
   | app = Term -> Term -> Term;

defn red : Term -> Term -> atom
  is red-lam  = [V : Term][F : Term -> Term] red (app (lam F) V) (F V)
   | red-app1 = [V1 : Term][V1' : Term][V2 : Term] red V1 V1' -> red (app V1 V2) (app V1' V2)
   | red-app2 = [V1 : Term][V2' : Term][V2 : Term] red V2 V2' -> red (app V1 V2) (app V1 V2');


query sum-1 = add (succ (succ zero)) 'v (succ (succ (succ zero)));
query sum-2 = add (succ (succ zero)) (succ (succ (succ zero))) 'v; 
