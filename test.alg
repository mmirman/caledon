defn num  : atom
  is zero = num
   | succ = num -> num;

defn List : atom -> atom
  is nil  = [A : atom] List A
   | cons = [A : atom] A -> List A -> List A;

defn add   : num -> num -> num -> atom
  is add-z = [N : num] add zero N N
   | add-s = [N : num][M : num][R : num] add N M R -> add (succ N) M (succ R);

query sum-1 = add (succ (succ zero)) 'v (succ (succ (succ zero)));
query sum-2 = add (succ (succ zero)) (succ (succ (succ zero))) 'v; 



