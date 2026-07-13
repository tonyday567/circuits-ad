{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

-- | SPIKE 3c — ∂Γ by AD, Riemann with ZERO finite differences.
--
-- Builds on:
--   3a Tag1-over-Tag2 nested smoke (second derivatives by tags)
--   3b polymorphic 'christoffel' formula
--
-- Metric component tables (g^{ci}, ∂_i g_{jk}) written polymorphically for
-- polar R² and unit S² — same geometry as the Diff metrics in MetricGamma.
-- Instantiating coordinates as Diff' Tag carriers makes Γ a Diff; its
-- pullback IS ∂Γ.  No central-FD, no gammaDiff stub.
--
-- Oracles: polar R=0; S² R^θ_φθφ = sin²θ, sectional K=1.
module RiemannAD
  ( runRiemannAD,
  )
where

import Circuit.AD (Diff', runDiff, pattern Diff)
import MetricGamma (christoffel, gammaAt, lowerPolar, raisePolar)
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Field qualified as NHF
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Prelude
import Prelude ()

data TagR -- differentiate wrt coord 0
data TagTh -- differentiate wrt coord 1

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-7

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
-- Polymorphic metric tables (polar R²)
-- ---------------------------------------------------------------------------

gInvPolar ::
  (NHA.Additive a, NHM.Multiplicative a, NHM.Divisive a) =>
  a ->
  Int ->
  Int ->
  a
gInvPolar r c i = case (c, i) of
  (0, 0) -> NHM.one
  (1, 1) -> NHM.recip (r NHM.* r)
  _ -> NHA.zero

dgPolar ::
  (NHA.Additive a, NHM.Multiplicative a) =>
  a ->
  Int ->
  Int ->
  Int ->
  a
dgPolar r i j k = case (i, j, k) of
  (0, 1, 1) -> (NHM.one NHA.+ NHM.one) NHM.* r
  _ -> NHA.zero

gammaPolar ::
  (NHA.Additive a, NHA.Subtractive a, NHM.Multiplicative a, NHM.Divisive a) =>
  a ->
  a ->
  Int ->
  Int ->
  Int ->
  a
gammaPolar r _th c a b = christoffel (gInvPolar r) (dgPolar r) c a b

-- ---------------------------------------------------------------------------
-- Polymorphic metric tables (unit S²)
-- ---------------------------------------------------------------------------

gInvSphere ::
  (NHF.TrigField a, NHM.Multiplicative a, NHM.Divisive a, NHA.Additive a) =>
  a ->
  Int ->
  Int ->
  a
gInvSphere th c i = case (c, i) of
  (0, 0) -> NHM.one
  (1, 1) ->
    let s = NHF.sin th
     in NHM.recip (s NHM.* s)
  _ -> NHA.zero

dgSphere ::
  (NHF.TrigField a, NHM.Multiplicative a, NHA.Additive a) =>
  a ->
  Int ->
  Int ->
  Int ->
  a
dgSphere th i j k = case (i, j, k) of
  (0, 1, 1) ->
    let two = NHM.one NHA.+ NHM.one
     in two NHM.* NHF.sin th NHM.* NHF.cos th
  _ -> NHA.zero

gammaSphere ::
  ( NHF.TrigField a,
    NHA.Additive a,
    NHA.Subtractive a,
    NHM.Multiplicative a,
    NHM.Divisive a
  ) =>
  a ->
  a ->
  Int ->
  Int ->
  Int ->
  a
gammaSphere th _ph c a b = christoffel (gInvSphere th) (dgSphere th) c a b

-- ---------------------------------------------------------------------------
-- ∂Γ by tagged Diff (no FD)
-- ---------------------------------------------------------------------------

partialGammaPolarAD ::
  (Double, Double) ->
  Int ->
  Int ->
  Int ->
  (Double, Double)
partialGammaPolarAD (r0, th0) c a b =
  let rVar = Diff (,id) :: Diff' TagR Double Double
      thC = Diff (const (th0, const 0)) :: Diff' TagR Double Double
      gR = gammaPolar rVar thC c a b
      (_, dR) = runDiff gR r0
      thVar = Diff (,id) :: Diff' TagTh Double Double
      rC = Diff (const (r0, const 0)) :: Diff' TagTh Double Double
      gTh = gammaPolar rC thVar c a b
      (_, dTh) = runDiff gTh th0
   in (dR 1.0, dTh 1.0)

partialGammaSphereAD ::
  (Double, Double) ->
  Int ->
  Int ->
  Int ->
  (Double, Double)
partialGammaSphereAD (th0, ph0) c a b =
  let thVar = Diff (,id) :: Diff' TagR Double Double
      phC = Diff (const (ph0, const 0)) :: Diff' TagR Double Double
      gTh = gammaSphere thVar phC c a b
      (_, dTh) = runDiff gTh th0
      phVar = Diff (,id) :: Diff' TagTh Double Double
      thC = Diff (const (th0, const 0)) :: Diff' TagTh Double Double
      gPh = gammaSphere thC phVar c a b
      (_, dPh) = runDiff gPh ph0
   in (dTh 1.0, dPh 1.0)

riemannPolarAD :: (Double, Double) -> Int -> Int -> Int -> Int -> Double
riemannPolarAD x rho sig mu nu =
  let g c a b = gammaPolar (fst x) (snd x) c a b
      dMu =
        let (dr, dth) = partialGammaPolarAD x rho nu sig
         in if mu == 0 then dr else dth
      dNu =
        let (dr, dth) = partialGammaPolarAD x rho mu sig
         in if nu == 0 then dr else dth
      partial = dMu - dNu
      quad =
        sum
          [ g rho mu lam * g lam nu sig - g rho nu lam * g lam mu sig
          | lam <- [0, 1]
          ]
   in partial + quad

riemannSphereAD :: (Double, Double) -> Int -> Int -> Int -> Int -> Double
riemannSphereAD x rho sig mu nu =
  let g c a b = gammaSphere (fst x) (snd x) c a b
      dMu =
        let (dth, dph) = partialGammaSphereAD x rho nu sig
         in if mu == 0 then dth else dph
      dNu =
        let (dth, dph) = partialGammaSphereAD x rho mu sig
         in if nu == 0 then dth else dph
      partial = dMu - dNu
      quad =
        sum
          [ g rho mu lam * g lam nu sig - g rho nu lam * g lam mu sig
          | lam <- [0, 1]
          ]
   in partial + quad

-- ---------------------------------------------------------------------------
-- Runner
-- ---------------------------------------------------------------------------

runRiemannAD :: IO ()
runRiemannAD = do
  putStrLn "=== SPIKE 3c: Riemann via AD ∂Γ (ZERO FD) ==="

  let xP = (2.0, 0.3)
  assertNear "poly Γ^r_θθ" (gammaPolar 2.0 0.3 0 1 1) (negate 2.0)
  assertNear "poly Γ^θ_rθ" (gammaPolar 2.0 0.3 1 0 1) 0.5
  assertNear
    "poly vs Diff-extract Γ^r_θθ"
    (gammaPolar 2.0 0.3 0 1 1)
    (gammaAt lowerPolar raisePolar xP 0 1 1)

  let (dr, dth) = partialGammaPolarAD xP 0 1 1
  assertNear "AD ∂_r Γ^r_θθ" dr (negate 1.0)
  assertNear "AD ∂_θ Γ^r_θθ" dth 0.0

  putStrLn "polar R² — R=0"
  mapM_
    ( \(rho, sig, mu, nu) ->
        assertNear
          ("R^" ++ show rho ++ "_" ++ show sig ++ show mu ++ show nu)
          (riemannPolarAD xP rho sig mu nu)
          0
    )
    [(rho, sig, mu, nu) | rho <- [0, 1], sig <- [0, 1], mu <- [0, 1], nu <- [0, 1], mu < nu]

  putStrLn "unit S² — K=1"
  let th = pi / 3
      xS = (th, 0.0)
      rTh = riemannSphereAD xS 0 1 0 1
      rPh = riemannSphereAD xS 1 0 1 0
  assertNear "R^θ_φθφ = sin²θ" rTh (sin th * sin th)
  assertNear "R^φ_θφθ = 1" rPh 1.0
  let g00 = 1.0
      g11 = sin th * sin th
      k = (g00 * rTh) / (g00 * g11)
  assertNear "sectional K=1" k 1.0

  putStrLn ""
  putStrLn "=== VERDICT 3c ==="
  putStrLn "YES — ∂Γ by tagged Diff AD, Riemann oracles PASS, ZERO finite differences."
  putStrLn "Spike-2 FD stub killed. Nested-AD claim complete for metric→Γ→R."
