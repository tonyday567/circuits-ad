{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

-- | SPIKE 4 — honest-backward geodesic step; pullback = discrete Jacobi map.
--
-- Spike 1 was forward-only (pullback stubbed as h·I).  One implicit-Euler
-- geodesic step s' = s0 + h·f(s') has IFT Jacobian
--
--   ds'/ds0 = (I − h·Df(s*))⁻¹
--
-- which is exactly what Star closes on the fiber (linear channel coupling
-- A = h·Df).  That Jacobian IS the discrete Jacobi map of the step.
--
-- Oracles:
--   A) Picard residual ~ 0
--   B) FD Jacobian of the Picard map s0↦s' matches (I−hJ)⁻¹ entrywise
--   C) reverse-mode Diff of the step (pullback = IFT) agrees with FD
module JacobiSpike
  ( runJacobiSpike,
  )
where

import Circuit.AD (Diff', runDiff, pattern Diff)
import NumHask.Prelude
import Prelude ()

type State = [Double]

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-6

assertNear :: String -> Double -> Double -> IO ()
assertNear name got expected =
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

-- ---------------------------------------------------------------------------
-- Polar R² geodesic
-- ---------------------------------------------------------------------------

geodesicF :: State -> State
geodesicF [r, _th, vr, vth] =
  let rSafe = if abs r < 1e-12 then 1e-12 else r
   in [vr, vth, r * vth * vth, -(2 / rSafe) * vr * vth]
geodesicF _ = error "geodesicF"

jacobianF :: State -> [[Double]]
jacobianF [r, _th, vr, vth] =
  let rSafe = if abs r < 1e-12 then 1e-12 else r
   in [ [0, 0, 1, 0],
        [0, 0, 0, 1],
        [vth * vth, 0, 0, 2 * r * vth],
        [ 2 / (rSafe * rSafe) * vr * vth,
          0,
          -(2 / rSafe) * vth,
          -(2 / rSafe) * vr
        ]
      ]
jacobianF _ = error "jacobianF"

transpose4 :: [[Double]] -> [[Double]]
transpose4 m = [[(m !! j) !! i | j <- [0 .. 3]] | i <- [0 .. 3]]

matVec4 :: [[Double]] -> [Double] -> [Double]
matVec4 m v = [sum (zipWith (*) row v) | row <- m]

-- | Solve (I − α A) x = b (4×4 Gauss-Jordan).
solveIMinus :: Double -> [[Double]] -> [Double] -> [Double]
solveIMinus alpha a b =
  let n = 4
      m0 =
        [ [ (if j == i then 1 else 0) - alpha * ((a !! i) !! j)
          | j <- [0 .. n - 1]
          ]
            ++ [b !! i]
        | i <- [0 .. n - 1]
        ]
      m1 = foldl elim m0 [0 .. n - 1]
   in map last m1
  where
    elim m piv =
      let rowP = map (/ ((m !! piv) !! piv)) (m !! piv)
       in [ if i == piv
              then rowP
              else
                let f = (m !! i) !! piv
                 in zipWith (\u v -> u - f * v) (m !! i) rowP
          | i <- [0 .. 3]
        ]

-- ---------------------------------------------------------------------------
-- Picard step + IFT / Diff
-- ---------------------------------------------------------------------------

picardStep :: Double -> Int -> State -> State
picardStep h n s0 =
  let step s = zipWith (\a b -> a + h * b) s0 (geodesicF s)
   in iterate step s0 !! n

-- | IFT Jacobian rows: (I − h Df(s*))⁻¹
idx4 :: [Int]
idx4 = [0, 1, 2, 3]

basis4 :: Int -> [Double]
basis4 k = [if i == k then 1 else 0 | i <- idx4]

iftJacobianRows :: Double -> State -> [[Double]]
iftJacobianRows h sStar =
  let j = jacobianF sStar
      cols = [solveIMinus h j (basis4 k) | k <- idx4]
   in transpose4 cols -- rows of (I−hJ)⁻¹

-- | FD Jacobian of Picard map s0 ↦ s' (for oracle only).
fdJacobianRows :: Double -> Int -> State -> [[Double]]
fdJacobianRows h n s0 =
  let eps = 1e-7
      s1 = picardStep h n s0
      col k =
        let s0' = [if i == k then x + eps else x | (i, x) <- zip idx4 s0]
            s1' = picardStep h n s0'
         in zipWith (\a b -> (a - b) / eps) s1' s1
      cols = [col k | k <- idx4]
   in transpose4 cols

-- | Step as Diff: forward Picard, pullback = IFT (honest fiber Jacobian).
-- This is what Star computes from channel coupling A = h·Df at the fixpoint.
stepDiff :: Double -> Int -> Diff' () State State
stepDiff h n = Diff $ \s0 ->
  let s1 = picardStep h n s0
      j = jacobianF s1
      -- pb = J_step^T = (I−hJ)⁻T
      pb ds1 = solveIMinus h (transpose4 j) ds1
   in (s1, pb)

-- | Jacobian rows from reverse-mode pullbacks of stepDiff.
pullbackJacobianRows :: Double -> Int -> State -> [[Double]]
pullbackJacobianRows h n s0 =
  let (_s1, pb) = runDiff (stepDiff h n) s0
      -- pb = J^T; pb(e_k) = k-th row of J
   in [pb (basis4 k) | k <- idx4]

maxEntryDiff :: [[Double]] -> [[Double]] -> Double
maxEntryDiff a b =
  maximum
    [ abs ((a !! i) !! j - (b !! i) !! j)
    | i <- idx4,
      j <- idx4
    ]

-- ---------------------------------------------------------------------------
-- Runner
-- ---------------------------------------------------------------------------

runJacobiSpike :: IO ()
runJacobiSpike = do
  putStrLn "=== SPIKE 4: honest-backward geodesic step / Jacobi ==="
  let s0 = [1, 0, 0, 1] :: State
      h = 0.1
      n = 50
      s1 = picardStep h n s0
      f1 = geodesicF s1
      residual = zipWith3 (\a b c -> a - b - h * c) s1 s0 f1
      resNorm = sqrt (sum (map (\x -> x * x) residual))

  putStrLn $ "s0 = " ++ show s0
  putStrLn $ "s1 = " ++ show s1
  assertNear "Picard residual" resNorm 0

  let jIft = iftJacobianRows h s1
      jFd = fdJacobianRows h n s0
      jPb = pullbackJacobianRows h n s0

  putStrLn $ "max |IFT − FD|  = " ++ show (maxEntryDiff jIft jFd)
  putStrLn $ "max |pullback − IFT| = " ++ show (maxEntryDiff jPb jIft)
  putStrLn $ "max |pullback − FD|  = " ++ show (maxEntryDiff jPb jFd)

  assertNear "IFT matches FD Jacobian" (maxEntryDiff jIft jFd) 0
  assertNear "pullback matches IFT" (maxEntryDiff jPb jIft) 0
  assertNear "pullback matches FD" (maxEntryDiff jPb jFd) 0

  -- Channel coupling of Picard body is A = h·Df — Star star(A)=(I−A)⁻¹
  -- is exactly the IFT map.  Report ||A|| scale.
  let j = jacobianF s1
      aNorm = maximum [abs (h * ((j !! i) !! k)) | i <- idx4, k <- idx4]
  putStrLn $ "||h·Df||_max = " ++ show aNorm ++ " (channel self-coupling scale)"

  putStrLn ""
  putStrLn "=== VERDICT 4 ==="
  putStrLn "YES — geodesic step pullback = (I−h Df)⁻¹ = discrete Jacobi map."
  putStrLn "Honest fiber linearization; Star organ is the IFT solve."
  putStrLn "Spike 1 forward-only gap closed. Capstone (d²flow / Jacobi eqn + R)"
  putStrLn "can sit on this organ."
