{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import qualified AST as A
import qualified Context as C
import Choice
import qualified HOU as H
import qualified Substitution as S
import qualified Src.AST as B
import qualified Src.HOU as B
import qualified Src.LatticeUnify as L
import qualified Src.Reconstruction as R
import qualified Src.Substitution as BS
import qualified Src.Translate as T
import Universe
import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Except (catchError)
import Control.Monad.RWS.Strict (runRWST)
import Control.Monad.State (evalStateT)
import Data.List (permutations)
import Data.Either (isLeft)
import qualified Data.Map.Strict as M
import System.Exit
import System.Process
import System.Timeout

runChoice :: Choice a -> Either String a
runChoice = runError

assertThat :: String -> Bool -> IO ()
assertThat label b = unless b $ error label

check :: String -> IO () -> IO Bool
check name test = do
  result <- timeout (30 * 1000000) (try test)
  case result of
    Just (Right ()) -> putStrLn ("PASS " ++ name) >> return True
    Just (Left (e :: SomeException)) -> putStrLn ("FAIL " ++ name ++ ": " ++ take 1600 (show e)) >> return False
    Nothing -> putStrLn ("FAIL " ++ name ++ ": timed out") >> return False

universeTests :: IO ()
universeTests = do
  -- Exhaust all directed graphs on three vertices, with absent, <=, or <
  -- at each edge. Independently enumerate all assignments in {0,1,2}^3.
  let names = ["a","b","c"]
      pairs = [(a,b) | a <- names, b <- names]
      graphs = sequence [[Nothing, Just (a :<=: b), Just (a :<: b)] | (a,b) <- pairs]
      assignments = map (M.fromList . zip names) (replicateM 3 [0..2])
      satisfies levels (a :<=: b) = levels M.! a <= levels M.! b
      satisfies levels (a :<: b) = levels M.! a < levels M.! b
      insert gr (a :<=: b) = L.insLTE gr a b
      insert gr (a :<: b) = L.insLT gr a b
  forM_ graphs $ \g -> do
    let constraints = [c | Just c <- g]
        witnesses = filter (\m -> all (satisfies m) constraints) assignments
        solved = solveUniverses constraints
    assertThat ("satisfiability mismatch: " ++ show constraints) $
      isUniverseGraph constraints == not (null witnesses)
    case solved of
      Nothing -> return ()
      Just levels -> do
        assertThat "invalid certificate" $ all (satisfies levels) constraints
        assertThat "assignment is not least" $
          all (\m -> all (\(v,k) -> k <= m M.! v) (M.toList levels)) witnesses
    forM_ [constraints, reverse constraints] $ \cs ->
      assertThat "incremental/order-dependent universe mismatch" $
        (not $ isLeft $ runChoice $ foldM insert L.newGraph cs >>= L.validateGraph) == not (null witnesses)

choiceTests :: IO ()
choiceTests = do
  let branch = appendErr "context" (pure (1::Int) <|> pure 2)
      continuation x = if x == 2 then pure x else Fail "try again"
      infinite = infinite :<|>: infinite :: Choice Int
  assertThat "backtracking lost a successful continuation" $
    runChoice (branch >>= continuation) == Right 2
  assertThat "breadth-first search is not fair" $
    runChoice (infinite <|> pure 7) == Right 7
  assertThat "error handler discarded alternatives" $
    runChoice (catchError (pure 1 <|> pure 2) (const (pure 3)) >>= continuation) == Right 2

legacyUnify :: A.Constraint -> Either String S.Substitution
legacyUnify c = fmap (\(s,_,_) -> s) $ runChoice $ runRWST (H.unify c) env C.emptyState
  where env = M.union A.envConsts $ M.fromList
          [("o", A.anonymous A.tipe), ("c", A.anonymous o), ("d", A.anonymous o),
           ("s", A.anonymous (o A.~> o))]
        o = A.var "o"

normal :: A.Spine -> B.N
normal = BS.etaReduce . T.fromSpine . S.etaReduce

legacyUnificationTests :: IO ()
legacyUnificationTests = do
  let o = A.var "o"
      x = A.var "x"; y = A.var "y"
      f args = A.Spine "F" args
      bind q n ty = A.Bind q n ty
      accepts label wrapper a b = case legacyUnify (wrapper $ A.SCons [a A.:=: b]) of
        Left e -> error (label ++ ": " ++ e)
        Right sub -> assertThat (label ++ ": substitution does not solve the original equation") $
          normal (S.subst sub a) == normal (S.subst sub b)
      rejects label c = assertThat label $ isLeft $ legacyUnify c
      quantify = bind A.Exists "F" (o A.~> o A.~> o) . bind A.Forall "x" o . bind A.Forall "y" o
  forM_ (permutations [x,y]) $ \args -> do
    accepts "projection" quantify (f args) x
    accepts "constant imitation" quantify (f args) (A.Spine "s" [x])
  let z = A.var "z"
      quantify3 = bind A.Exists "F" (o A.~> o A.~> o A.~> o)
                . bind A.Forall "x" o . bind A.Forall "y" o . bind A.Forall "z" o
      targets = [x,y,z,A.var "c"]
      successor t = A.Spine "s" [t]
  forM_ (permutations [x,y,z]) $ \args ->
    forM_ (targets ++ map successor targets ++ map (successor . successor) targets) $ \rhs ->
      accepts "generated named pattern" quantify3 (f args) rhs
  accepts "same flex head / pruning" quantify (f [x,y]) (f [y,x])
  accepts "different flex heads" (bind A.Exists "G" (o A.~> o) . quantify)
    (f [x,y]) (A.Spine "G" [y])
  accepts "scope raising" (bind A.Exists "F" (o A.~> o) . bind A.Forall "x" o . bind A.Exists "G" o)
    (f [x]) (A.var "G")
  rejects "distinct rigid constants unified" (A.SCons [A.var "c" A.:=: A.var "d"])
  rejects "occurs check accepted F = s F" $ bind A.Exists "F" o $ A.SCons [f [] A.:=: A.Spine "s" [f []]]
  rejects "escaped bound variable" $ bind A.Exists "F" o $ bind A.Forall "x" o $ A.SCons [f [] A.:=: x]

substitutionTests :: IO ()
substitutionTests = do
  let o = A.var "o"
      term = A.Abs "1" o (A.Abs "x" o (A.var "1"))
      restored = S.rebuildFromMem (M.singleton "1" "x") term
  assertThat "restoring names captured an outer variable" $ normal restored == normal term
  let open = A.Abs "x" o (A.var "1")
      renamed = S.rebuildFromMem (M.singleton "1" "x") open
  assertThat "restoring names captured a free variable" $
    normal renamed == normal (A.Abs "z" o (A.var "x"))
  let sub = M.singleton "x" (A.var "y")
  assertThat "substitution captured a free variable" $
    normal (S.subst sub (A.Abs "y" o (A.var "x"))) == normal (A.Abs "z" o (A.var "y"))

newUnificationTests :: IO ()
newUnificationTests = do
  let o = B.vcon "o"
      cons = M.union B.constants $ M.fromList
        [("o", B.constant $ B.tipemake "u"), ("c", B.constant o), ("d", B.constant o),
         ("s", B.constant (o B.~> o))]
      solve c = runChoice $ evalStateT (B.unifyAll B.newGraph cons c) 0
      accepts label c a b = case solve c of
        Left e -> error (label ++ ": " ++ e)
        Right (_,r) -> assertThat (label ++ ": invalid reconstruction") $
          BS.etaReduce (R.substReconstruct r a) == BS.etaReduce (R.substReconstruct r b)
      rejects label c = assertThat label $ isLeft $ solve c
      f = B.evar 0 "F" o
  accepts "new constant imitation" (f B.:=: B.con "c") f (B.con "c")
  rejects "new distinct rigid constants unified" (B.con "c" B.:=: B.con "d")
  rejects "new strict universe reflexivity" (B.Pat (B.tipemake "u") B.:<: B.Pat (B.tipemake "u"))
  rejects "new mixed universe cycle" $
    (B.Pat (B.tipemake "a") B.:<: B.Pat (B.tipemake "b")) B.:&:
    (B.Pat (B.tipemake "b") B.:<=: B.Pat (B.tipemake "c")) B.:&:
    (B.Pat (B.tipemake "c") B.:<=: B.Pat (B.tipemake "a"))
  rejects "new occurs check" (f B.:=: B.Pat (B.vcon "s" B.:+: f))
  rejects "new escaped bound variable" $ B.Bind o $ f B.:=: B.var 0
  let f2 a b = B.Pat $ B.evvar 0 "F" (o B.~> o B.~> o) B.:+: B.var a B.:+: B.var b
      g1 a = B.Pat $ B.evvar 0 "G" (o B.~> o) B.:+: B.var a
  accepts "new same flex head / pruning"
    (B.Bind o $ B.Bind o $ f2 1 0 B.:=: f2 0 1) (f2 1 0) (f2 0 1)
  accepts "new different flex heads"
    (B.Bind o $ B.Bind o $ f2 1 0 B.:=: g1 0) (f2 1 0) (g1 0)
  let outer = B.Pat $ B.evvar 0 "F" (o B.~> o) B.:+: B.var 0
      inner = B.evar 1 "G" o
  accepts "new scope raising" (B.Bind o $ outer B.:=: inner) outer inner
  forM_ (permutations [0,1]) $ \args -> do
    let lhs = B.Pat $ foldl (B.:+:) (B.evvar 0 "F" (o B.~> o B.~> o)) (map B.var args)
        rhs = B.var 0
    accepts "new projection" (B.Bind o $ B.Bind o $ lhs B.:=: rhs) lhs rhs

  let f3 args = B.Pat $ foldl (B.:+:) (B.evvar 0 "F" (o B.~> o B.~> o B.~> o)) (map B.var args)
      targets = map B.var [0,1,2] ++ [B.con "c"]
      successor t = B.Pat $ B.vcon "s" B.:+: t
  forM_ (permutations [0,1,2]) $ \args ->
    forM_ (targets ++ map successor targets ++ map (successor . successor) targets) $ \rhs ->
      accepts "generated de Bruijn pattern" (B.Bind o $ B.Bind o $ B.Bind o $ f3 args B.:=: rhs) (f3 args) rhs

certificateTests :: IO ()
certificateTests = do
  let level n = A.Spine "type" [A.var n]
      verify tm ty = runChoice $ H.inferUniverseLevels "test certificate" M.empty tm ty
  assertThat "Type u : Type u was accepted" $ isLeft $ verify (level "u") (level "u")
  assertThat "Type u : Type v was rejected" $ not $ isLeft $ verify (level "u") (level "v")
  let o = A.var "o"
      env = M.fromList [("o",A.tipe),("c",o),("f",o A.~> o)]
      check tm ty = runChoice $ H.inferUniverseLevels "test certificate" env tm ty
  assertThat "valid ground certificate rejected" $ not $ isLeft $ check (A.var "c") o
  assertThat "invalid ground certificate accepted" $ isLeft $ check (A.var "c") A.tipe
  assertThat "invalid application certificate accepted" $ isLeft $ check (A.Spine "c" [A.var "c"]) o

cli :: FilePath -> Bool -> IO ()
cli path success = do
  (code,out,err) <- readProcessWithExitCode "caledon" ["--io-only",path] ""
  assertThat (path ++ " returned " ++ show code ++ "\n" ++ take 1800 (out++err)) $
    (code == ExitSuccess) == success

main :: IO ()
main = do
  results <- sequence
    [ check "19,683 universe graphs: brute-force satisfiability, least certificates, insertion order" universeTests
    , check "choice backtracking and breadth-first fairness" choiceTests
    , check "named unifier: reconstructed substitutions, occurs check, scope" legacyUnificationTests
    , check "capture-avoiding substitution and name restoration" substitutionTests
    , check "de Bruijn unifier: reconstructed substitutions, rigid heads, universes" newUnificationTests
    , check "proof certificates and Type-in-Type rejection" certificateTests
    , check "CLI constructive theorems and higher-order proof search" $ cli "examples/theorems.ncc" True
    , check "CLI inferred higher-order function types" $ cli "examples/simple.ncc" True
    , check "CLI standard prelude" $ cli "prelude/prelude.ncc" True
    , check "CLI dependent universe encoding" $ cli "examples/universe.ncc" True
    , check "CLI HOAS linearity" $ cli "examples/linear.ncc" True
    , check "CLI higher-order search" $ cli "examples/higherOrder.ncc" True
    , check "CLI Church naturals" $ cli "examples/nat1.ncc" True
    , check "CLI polymorphic identity" $ cli "tests/fixtures/identity.ncc" True
    , check "CLI impossible proof fails" $ cli "tests/fixtures/empty.ncc" False
    , check "CLI invalid application fails" $ cli "tests/fixtures/bad-application.ncc" False
    , check "CLI malformed syntax fails" $ cli "tests/fixtures/malformed.ncc" False
    , check "CLI false equality fails" $ cli "tests/fixtures/occurs.ncc" False
    ]
  unless (and results) exitFailure
