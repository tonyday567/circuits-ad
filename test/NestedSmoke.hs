{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

-- | SPIKE 3a — scalar nested smoke.
--
-- Gate: nothing in the repo yet proves Tag nesting yields a correct SECOND
-- derivative number (Tags.hs only checks a nested primal).  This does.
--
-- f(x) = sin(x²)
-- f'(x) = 2x cos(x²)
-- f''(x) = 2 cos(x²) − 4x² sin(x²)
--
-- Nested carriers (numhask-diff design): write f once polymorphic; L1 =
-- Diff' Tag1; L2 = Diff' Tag1 over Diff' Tag2 scalars.  No finite differences.
module NestedSmoke
  ( runNestedSmoke,
  )
where

import Circuit.AD (Diff', runDiff, pattern Diff)
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Field qualified as NHF
import NumHask.Prelude
import Prelude ()

data Tag1

data Tag2

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-9

assert :: String -> Double -> Double -> IO ()
assert name got expected =
  if near got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else
      putStrLn $
        "  FAIL "
          ++ name
          ++ ": got "
          ++ show got
          ++ ", expected "
          ++ show expected

-- | Polymorphic f — one definition, many carriers.
fPoly :: (NHF.TrigField a, NHM.Multiplicative a) => a -> a
fPoly x = NHF.sin (x NHM.* x)

-- | Analytic derivatives for oracle.
f'Analytic :: Double -> Double
f'Analytic x = 2 * x * cos (x * x)

f''Analytic :: Double -> Double
f''Analytic x = 2 * cos (x * x) - 4 * x * x * sin (x * x)

-- | L1 reverse-mode: instantiate at Diff' Tag1 Double Double.
firstDeriv :: Double -> Double
firstDeriv x0 =
  let x = Diff (,id) :: Diff' Tag1 Double Double
      f = fPoly x
      (_, pb) = runDiff f x0
   in pb 1.0

-- | Outer carrier for nesting.
type Outer = Diff' Tag2 Double Double

-- | L2 nested reverse-over-reverse: Diff' Tag1 over Outer = Diff' Tag2 Double Double.
--
--   seed  = identity Outer
--   xI    = identity Tag1 on Outer
--   fI    = fPoly xI          -- Tag1 Diff whose values are Outer Diffs
--   pbS 1 = first derivative as an Outer Diff
--   runDiff (pbS 1) x0  →  (f', f'')
secondDeriv :: Double -> (Double, Double)
secondDeriv x0 =
  let seed = Diff (,id) :: Outer
      oneO = NHM.one :: Outer -- constant-1 Outer Diff
      xI = Diff (,id) :: Diff' Tag1 Outer Outer
      fI = fPoly xI
      (_yS, pbS) = runDiff fI seed
      -- first derivative as Outer Diff; differentiate it at x0
      gOuter = pbS oneO
      (g1, gPb) = runDiff gOuter x0
   in (g1, gPb 1.0)

runNestedSmoke :: IO ()
runNestedSmoke = do
  putStrLn "=== SPIKE 3a: scalar nested smoke f=sin(x²) ==="
  let x0 = 1.5
      f1 = firstDeriv x0
      (g1, g2) = secondDeriv x0
      a1 = f'Analytic x0
      a2 = f''Analytic x0
  putStrLn $ "x0 = " ++ show x0
  putStrLn $ "analytic f'  = " ++ show a1
  putStrLn $ "analytic f'' = " ++ show a2
  assert "L1 first deriv (Tag1)" f1 a1
  assert "L2 first deriv (nested, value)" g1 a1
  assert "L2 second deriv (Tag1-over-Tag2)" g2 a2

  -- second point
  let x1 = 0.7
      (_, g2') = secondDeriv x1
  assert "L2 f'' at 0.7" g2' (f''Analytic x1)

  putStrLn ""
  putStrLn "=== VERDICT 3a ==="
  if near g2 a2
    then putStrLn "YES — Tag nesting yields correct f''. Gate open for 3b/3c."
    else putStrLn "NO — nested second derivative wrong; gate closed."
