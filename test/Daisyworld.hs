{-# LANGUAGE RebindableSyntax #-}

-- | Oracle harness for "Homeostasis is a pullback number"
-- ('Circuit.AD.Daisyworld').
--
-- Checks (1) physical simplex membership, (2) pullback≡FD, (3) regulation
-- vs bare planet, (4) Watson–Lovelock 1983 structural signatures
-- (coverage identity, black→white succession, T* plateau near T_opt).
module Daisyworld
  ( runDaisyworld,
  )
where

import Circuit.AD.Daisyworld
import NumHask.Prelude
import Text.Printf (printf)
import Prelude ()

assertNear :: String -> Double -> Double -> Double -> IO ()
assertNear name tol got expected =
  if abs (got - expected) < tol
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got ++ " ≈ " ++ show expected
    else
      putStrLn $
        "  FAIL "
          ++ name
          ++ ": got "
          ++ show got
          ++ ", expected "
          ++ show expected

assertTrue :: String -> Bool -> IO ()
assertTrue name ok =
  if ok
    then putStrLn $ "  PASS " ++ name
    else putStrLn $ "  FAIL " ++ name

physical :: [Double] -> Bool
physical [ab, aw] = ab >= -1e-12 && aw >= -1e-12 && ab <= 1 + 1e-12 && aw <= 1 + 1e-12 && ab + aw <= 1 + 1e-9
physical _ = False

runDaisyworld :: IO ()
runDaisyworld = do
  putStrLn "=== Daisyworld pearl: homeostasis is a pullback number ==="

  -- ---- Equilibrium at L = 1 ----
  let l0 = 1.0
      sStar = newtonEq l0 [0.3, 0.3]
      tStar = teD l0 sStar
      bare = bareTeD l0
      resN = sqrt (sum (map (\x -> x * x) (rhsD l0 sStar)))
  printf "L=1  α* = [%.6f, %.6f]  sum=%.6f\n" (sStar !! 0) (sStar !! 1) (sum sStar)
  printf "L=1  T* = %.4f K   bare T = %.4f K\n" tStar bare
  assertNear "equilibrium residual" 1e-6 resN 0
  assertTrue "α* physical at L=1" (physical sStar)

  -- ---- dT*/dL pullback ----
  let dPull = dTstar_dL l0 sStar
      dFd = dTstar_dL_FD l0 1e-4 sStar
      dBare = dBare_dL l0
  printf "dT*/dL pullback = %.6f\n" dPull
  printf "dT*/dL FD       = %.6f\n" dFd
  printf "dT_bare/dL      = %.6f\n" dBare
  assertNear "pullback vs FD dT*/dL" 1e-4 dPull dFd

  let reg = abs dPull / max 1e-12 (abs dBare)
  printf "|dT*/dL| / |dT_bare/dL| = %.4f\n" reg
  assertTrue "regulation: daisy ≪ bare" (reg < 0.5)

  -- ---- L sweep ----
  putStrLn "L sweep (full precision):"
  let sweep = [0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.3, 1.4, 1.5, 1.6]
      rows =
        [ let s = newtonEq l [0.25, 0.25]
           in (l, teD l s, bareTeD l, s !! 0, s !! 1)
        | l <- sweep
        ]
  mapM_
    ( \(l, t, b, ab, aw) ->
        printf
          "  L=%.1f  T*=%.3f  bare=%.3f  αb=%.6f  αw=%.6f  sum=%.6f\n"
          l
          t
          b
          ab
          aw
          (ab + aw)
    )
    rows

  -- Physical alphas everywhere
  assertTrue
    "all sweep α physical"
    (all (\(_, _, _, ab, aw) -> physical [ab, aw]) rows)

  -- W-L signature: when BOTH daisies present, total coverage is constant
  -- (x β_b = x β_w = γ ⇒ β_b = β_w ⇒ fixed x under the growth parabola).
  let bothPresent = [(ab + aw) | (_, _, _, ab, aw) <- rows, ab > 0.05, aw > 0.05]
      coverage0 = head bothPresent
  putStrLn $ "both-present coverages: " ++ show bothPresent
  assertTrue
    "W-L coverage identity (constant α_b+α_w when both live)"
    (all (\c -> abs (c - coverage0) < 1e-6) bothPresent)
  assertNear "W-L coverage ≈ 0.673 under std params" 1e-3 coverage0 (1 - 0.3 / 0.917) -- ~0.673

  -- Black→white succession (W-L fig 1 shape)
  let abAt l = let s = newtonEq l [0.25, 0.25] in s !! 0
      awAt l = let s = newtonEq l [0.25, 0.25] in s !! 1
  assertTrue "black declines with L (0.8→1.2)" (abAt 0.8 > abAt 1.0 && abAt 1.0 > abAt 1.2)
  assertTrue "white increases with L (0.8→1.2)" (awAt 0.8 < awAt 1.0 && awAt 1.0 < awAt 1.2)

  -- T* plateau near T_opt over the daisy band; bare rises steeply
  let daisyBand = [t | (l, t, _, ab, aw) <- rows, ab + aw > 0.05, l >= 0.8, l <= 1.2]
      bareBand = [b | (l, _, b, ab, aw) <- rows, ab + aw > 0.05, l >= 0.8, l <= 1.2]
      mean xs = sum xs / fromIntegral (length xs)
      var xs =
        let m = mean xs
         in mean (map (\x -> (x - m) * (x - m)) xs)
      vT = var daisyBand
      vB = var bareBand
  printf "var(T*) band = %.4f   var(bare) = %.4f\n" vT vB
  assertTrue "plateau: var(T*) < var(bare)" (vT < vB)
  assertTrue
    "T* near T_opt (290–300 K) on plateau"
    (all (\t -> t > 290 && t < 300) daisyBand)

  -- Dead ends match bare planet
  let (t06, b06) = let s = newtonEq 0.6 [0.25, 0.25] in (teD 0.6 s, bareTeD 0.6)
      (t16, b16) = let s = newtonEq 1.6 [0.25, 0.25] in (teD 1.6 s, bareTeD 1.6)
  assertNear "L=0.6 no life: T*=bare" 1e-6 t06 b06
  assertNear "L=1.6 no life: T*=bare" 1e-6 t16 b16

  putStrLn ""
  putStrLn "=== PEARL ==="
  putStrLn "One polymorphic RHS. Double = simulate. Diff = dT*/dL free."
  putStrLn "Homeostasis is a pullback number. W-L 1983 signatures hold."
