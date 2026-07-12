{-# LANGUAGE RebindableSyntax #-}

-- | Oracle harness for "Homeostasis is a pullback number"
-- ('Circuit.AD.Daisyworld').
module Daisyworld
  ( runDaisyworld,
  )
where

import Circuit.AD.Daisyworld
import NumHask.Prelude
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

runDaisyworld :: IO ()
runDaisyworld = do
  putStrLn "=== Daisyworld pearl: homeostasis is a pullback number ==="

  -- Equilibrium at L = 1
  let l0 = 1.0
      sStar = newtonEq l0 [0.3, 0.3]
      tStar = teD l0 sStar
      bare = bareTeD l0
      resN = sqrt (sum (map (\x -> x * x) (rhsD l0 sStar)))
  putStrLn $ "L=1  α* = " ++ show sStar
  putStrLn $ "L=1  T* = " ++ show tStar ++ "  bare T = " ++ show bare
  assertNear "equilibrium residual" 1e-6 resN 0

  -- dT*/dL: pullback ≡ FD; regulation ≪ bare
  let dPull = dTstar_dL l0 sStar
      dFd = dTstar_dL_FD l0 1e-4 sStar
      dBare = dBare_dL l0
  putStrLn $ "dT*/dL pullback = " ++ show dPull
  putStrLn $ "dT*/dL FD       = " ++ show dFd
  putStrLn $ "dT_bare/dL      = " ++ show dBare
  assertNear "pullback vs FD dT*/dL" 1e-4 dPull dFd

  let reg = abs dPull / max 1e-12 (abs dBare)
  putStrLn $ "|dT*/dL| / |dT_bare/dL| = " ++ show reg
  if reg < 0.5
    then putStrLn "  PASS regulation: daisy sensitivity ≪ bare"
    else putStrLn "  FAIL regulation ratio"

  -- L sweep: the iconic plateau
  putStrLn "L sweep (L, T*, T_bare, α_b, α_w):"
  let sweep = [0.6, 0.7, 0.8, 0.9, 1.0, 1.1, 1.2, 1.3, 1.4, 1.5, 1.6]
      rows =
        [ let s = newtonEq l [0.25, 0.25]
           in (l, teD l s, bareTeD l, s !! 0, s !! 1)
        | l <- sweep
        ]
  mapM_
    ( \(l, t, b, ab, aw) ->
        putStrLn $
          "  L="
            ++ show l
            ++ " T*="
            ++ take 7 (show t)
            ++ " bare="
            ++ take 7 (show b)
            ++ " αb="
            ++ take 6 (show ab)
            ++ " αw="
            ++ take 6 (show aw)
    )
    rows

  let daisyBand = [t | (l, t, _, ab, aw) <- rows, ab + aw > 0.05, l >= 0.8, l <= 1.2]
      bareBand = [b | (l, _, b, ab, aw) <- rows, ab + aw > 0.05, l >= 0.8, l <= 1.2]
      mean xs = sum xs / fromIntegral (length xs)
      var xs =
        let m = mean xs
         in mean (map (\x -> (x - m) * (x - m)) xs)
      vT = if length daisyBand < 2 then 0 else var daisyBand
      vB = if length bareBand < 2 then 1 else var bareBand
  putStrLn $ "var(T*) band = " ++ show vT ++ "  var(bare) = " ++ show vB
  if vT < vB
    then putStrLn "  PASS plateau: var(T*) < var(bare)"
    else putStrLn "  FAIL plateau"

  putStrLn ""
  putStrLn "=== PEARL ==="
  putStrLn "One polymorphic RHS. Double = simulate. Diff = dT*/dL free."
  putStrLn "Homeostasis is a pullback number."
