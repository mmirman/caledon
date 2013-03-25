Caledon Language ![logo](https://raw.github.com/mmirman/caledon/hopa/media/logo.png)
====================================================================================

Caledon is a dependently typed, polymorphic, higher order logic programming language. ie, everything you need to have a conversation with your computer.

Background
----------

* This is part of my masters thesis.  Feedback would be appreciated. Considering this, it is still in the very early research stages.  Syntax is liable to change, there will be bugs, and it doesn't yet have IO (I'm still working out how to do IO cleanly, but this WILL come).

* It's named caledon after the "New Caledonian Crow" - a crow which can make tools and meta tools.  Since this language supports meta programming with holes, implicits, polymorphism, and dependent types, I thought this crow might be a good mascot. Also, file extensions are ".ncc"

* This language was inspired by twelf, haskell and agda.

Goals
-----

* Make logic programming less repetative

* A logic programming language that is good at defining DSLs

* A language/system for conversing with the machine in a manner less one sided and instructional than regular programming.

* Make automated theorem proving intuitive.  

Philosophies
------------

* Metaprogramming should be easy and thus first class.

* User facing code should not crash - runtime code should be type checked.

* Metacode should be optionally typechecked, but well type checked.

* Metaprogramming should not require AST traversal.

* Your programming language should be turing complete - totality checking is annoying.

* Syntax should be elegant.

* Primitives should be minimal, libraries should be extensive.  Learning a culture is easy if you speak the language.  Learning a language by cultural immersion isn't as trivial.

Usage
-----

* To install from hackage:

```
> cabal install caledon
```

* To install directly from source:

```
> git clone git://github.com/mmirman/caledon.git
> cd caledon
> cabal configure
> cabal install
```

* To run:

```
> caledon file.ncc
```

* Unicode syntax is possible in emacs using: 

```
M-x \ TeX <ENTER>
```

Features
--------

* Logic programming:  Currently it uses a breadth first proof search. This is done for completeness, since the proof search is also used in type inference.  This could (and should) possibly change in the future for the running semantics of the language.

```
defn num  : prop
   | zero = num
   | succ = num -> num

defn add  : num -> num -> num -> prop
   | add_zero = add zero N N
   | add_succ = add (succ N) M (succ R) <- add N M R

-- we can define subtraction from addition!
defn subtract : num -> num -> num -> prop
  as \a b c : num . add b c a

```

* Some basic IO: Using unix pipes, this Caledon can be used more seriously.  Somebody plz write a wrapper?

```
query main = run $ do 
                 , putStr "hey!\n"
	  	 , readLine (\A . do 
   		     , putStr A
                     , putStr "\nbye!\n")
```

* Higher order logic programming: like in twelf and lambda-prolog.  This makes HOAS much easier to do.

```
defn trm : prop
   | lam = (trm -> trm) -> trm
   | app = trm -> trm -> trm

-- we can check that a term is linear!
defn linear : (trm → trm) → prop
   | linear_var = linear ( λ v . v )
   | linear_lam = {N} linear (λ v . lam (λ x . N x v))
                ← [x] linear (λ v . N x v)
   | linear_app1 = {V}{F} linear (λ v . app (F v) V)
                        ← linear F
   | linear_app2 = ?∀ V . ?∀ F . linear (λ v . app F (V v))
                               ← linear V
```

* Calculus of Constructions:  This is now consistent, and still has similar expressive power!  Now any term must be terminating. Although term/proof search might not be
terminating, proof search can be used to search more intelligently for theorems in the term language.

```
defn maybe   : prop → prop
   | nothing = maybe A
   | just    = A → maybe A

infix 1 =:=
defn =:= : A -> A -> prop
   | eq = (=:=) {A = A} V V

infix 0 /\
defn /\ : prop -> prop -> prop
   | and = {a : prop}{b : prop} a -> b -> a /\ b

infixr 0 |->
defn |-> : [a : prop] [b : prop] prop
  as \a : prop . \b : prop . [ha : a] b
```

* Optional Unsound declarations:  Embedding certain terms has never been easier!  This way you can create recursive type definitions such as the well known "prop : prop".  

```
unsound tm : {S : tm ty} tm S → prop
   | ty  = tm ty
   | ♢   = tm ty -> tm ty
   | Π   = [T : tm ty] (tm T → tm T) → tm $ ♢ T
   | lam = [T : tm ty][F : tm T → tm T] tm {S = ♢ T} (Π A : T . F A)
   | raise = {T : tm ty} tm T → tm $ ♢ T
```

* Indulgent type inferring nondeterminism:  The entire type checking process is a nondeterministic search for a type check proof.  This could be massively slow, but at least it is complete.  The size of this search is bounded by the size of the types and not the whole program, so this shouldn't be too slow in practice.  (function cases should be small).  I'm working on adding search control primitives to make this more efficient.

* Holes:  types can have holes, terms can have holes.  The same proof search that is used in semantics is used in type inference, so you can use the same computational reasoning you use to program to reason about whether the type checker can infer types!  Holes get filled by a proof search on their type and the current context.  Since the entire type checking process is nondeterministic, if they get filled by a wrong term, they can always be filled again.

```
defn fsum_maybe  : (A -> B -> prop) -> maybe A -> maybe B → prop
   | fsum_nothing = [F : A -> B -> prop] maybe_fsum F nothing nothing
   | fsum_just    = [F : _ -> _ -> prop][av : A][bv : B]
                   maybe_fsum F (just av) (just bv)
                   <- F av bv
```

* Implicit arguments:  These are arguments that automagically get filled with holes when they need to be.  They form the basis for typeclasses (records to be added), although they are far more general. This is also where the language is most modern and interesting.  I'm curious to see what uses beyond typeclasses there are for these.

```
defn functor : (prop → prop) → prop
   | isFunctor = ∀ F . ({a}{b : _ } (a → b → prop) → F a → F b → prop) → functor F.

defn fsum : {F} functor F => {a}{b} (a → b → prop) → F a → F b → prop
   | get_fsum = [F] functor F -> [FSUM][Foo][Fa][Fb] FSUM Foo Fa Fb -> fsum Foo Fa Fb

defn functor_maybe : functor maybe -> prop.
   | is_functor_maybe = functor_maybe (isFunctor fsum_maybe).

-- this syntax is rather verbose for the moment.  I have yet to add typeclass syntax sugar.
```

* Nondeterminism control:  You can now control what patterns to match against sequentially versus concurrently.  This gives you massive control over program execution, and in the future might be implemented with REAL threads!

```
defn runBoth : bool -> prop
  >| run0 = runBoth A 
            <- putStr "tttt "
            <- A =:= true

   | run1 = runBoth A
            <- putStr "vvvv"
            <- A =:= true

   | run2 = runBoth A
            <- putStr "qqqq"
            <- A =:= true

  >| run3 = runBoth A
            <- putStr " jjjj"
            <- A =:= false

query main = runBoth false

-- main should print out something along the lines of "tttt vvqvqvqq jjjj"
```


* Arbitrary operator fixities:  combined with the calculus of constructions, you can nearly do agda style syntax (with a bit of creativity)!

```
defn bool : prop
   | true = bool
   | false = bool

defn if : bool -> bool
  as \b . b

infix 1 |:|
defn |:| : {a : prop} a -> a -> (a -> a -> a) -> a
  as ?\t : prop . \a b. \f : t -> t -> t. f a b

infix 0 ==>
defn ==> : {a : prop} bool -> ((a -> a -> a) -> a) -> a -> prop
   | thentrue =  [f : _ -> A] (true ==> f)  (f (\a b : A. a))
   | thenfalse = [f : _ -> A] (false ==> f) (f (\a b : A. b))

defn not : bool -> bool -> prop
  as \v . if v ==> false |:| true

```

* Optional unicode syntax: Monad m ⇒ ∀ t : goats . m (λ x : t . t → t).
    * implication :  "a -> b"  or "a → b" or "a <- b"  or "a ← b"
    * implicits:  "a => b"  or "a ⇒ b" or "a <= b"  or "a ⇐ b"
    * Quantification: "[x:A] t"  or  "∀ x:A . t" or "forall x:A . t"
    * abstraction: "λ x . t" or "\x.t"
    * Quantified implicits: "{x:A} t"  or  "?∀ x:A . t" or "?forall x:A . t"
    * implicit abstraction: "?λ x . t" or "?\x.t"



Primary Contributers
--------------------

* Author: Matthew Mirman

* Advisor: Frank Pfenning

Secondary Contributers
----------------------

* Samuel Gélineau (gelisam)

* Devin Nusbaum (el-devo)


