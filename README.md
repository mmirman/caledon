Caledon Language
================

Caledon is a dependently typed, polymorphic, higher order logic programming language. ie, everything you need to have a conversation with your computer.

Background
----------

* This is part of my masters thesis.  Feedback would be appreciated. 

* Its named caledon after the "New Caledonian Crow" - a crow which can make tools and meta tools.  Since this language supports meta programming with holes, implicits, polymorphism, and dependent types, I thought this crow might be a good masscot. Also, file suffixes are ".ncc" 

* This language was inspired by twelf, haskell and agda.  

Features
--------

* Logic programming:  Currently it uses a breadth first proof search. This is done for completeness, since the proof search is also used in type inference.  This could (and should) possibly change in the future for the running semantics of the language.  

* Higher order logic programming: like in twelf and lambda-prolog.  This makes HOAS much easier to do.  

* Indulgent type inferring nondeterminism:  The entire type checking process is a nondeterministic search for a type check proof.  This could be massively slow, but at least it is complete.  The size of this search is bounded by the size of the types and not the whole program, so this shouldn't be too slow in practice.  (function cases should be small).  I'm working on adding search control primitives to make this more efficient.

* Polymorphism:  This isn't sound. ie, atom : atom.  The unsoundness shouldn't be too problematic, since types are used for proof search and to ensure progress and not for theorem proving.  This language doesn't support totality, worlds, or universe checking yet, since it's goal is to be a query programming language.

* Closed types:  This is kind of a lie.  HOAS means you can introduce arbitrary types into the context and violate a closed type, and thus totality.  Be carefull when proving totality to yourself.

* Holes:  type can have holes, terms can have holes.  The same proof search that is used in semantics is used in type inference, so you can use the same computational reasoning you use to program to reason about whether the type checker can infer types!  Holes get filled by a proof search on their type and the current context.  Since the entire type checking process is nondeterministic, if they get filled by a wrong term, they can always be filled again.

* Implicit arguments:  These are arguments that automagically get filled with holes when they need to be.  They form the basis for typeclasses (records to be added), although they are far more general. This is also where the language is most modern and interesting.  I'm curious to see what uses beyond typeclasses there are for these.

* Optional unicode syntax: Monad m ⇒ ∀ t : goats . m (λ x : t . t → t)

Usage
-----

* To install, cabal install

* To run, caledon file.ncc

Examples
--------

* more to come.



