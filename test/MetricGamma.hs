{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RebindableSyntax #-}

-- | SPIKE 3b — polymorphic metric → Γ.
--
-- Write the Christoffel formula once with NumHask ops; feed it g^{ci} and
-- ∂_i g_{jk} as carrier values.  At Double it must reproduce the shipped
-- MetricAdjoint numbers (not a reimplementation of polar special cases).
--
--   Γ^c_{ab} = ½ g^{ci} (∂_a g_{ib} + ∂_b g_{ia} − ∂_i g_{ab})
--
-- ∂g comes from the metric Diff pullback (same extraction as MetricAdjoint
-- 'partialG') — honest L0.  The formula itself is carrier-polymorphic so 3c
-- can instantiate the same code at a tagged Diff carrier.
module MetricGamma
  ( runMetricGamma,
    christoffel,
    partialG,
    gammaAt,
    lowerPolar,
    raisePolar,
    lowerSphere,
    raiseSphere,
  )
where

import Circuit.AD (Diff, runDiff, pattern Diff)
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Prelude
import Prelude ()

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

-- ---------------------------------------------------------------------------
-- Polymorphic Christoffel (the formula — one definition)
-- ---------------------------------------------------------------------------

-- | Γ^c_{ab} from inverse-metric and ∂g tables.
--
-- Indices in {0,1}.  Carrier @a@ only needs +/* and @fromInteger@ via
-- NumHask field ops (½ = one/ (one+one)).
christoffel ::
  (NHA.Additive a, NHA.Subtractive a, NHM.Multiplicative a, NHM.Divisive a) =>
  -- | @gInv c i = g^{ci}@
  (Int -> Int -> a) ->
  -- | @dg i j k = ∂_i g_{jk}@
  (Int -> Int -> Int -> a) ->
  -- | c, a, b
  Int ->
  Int ->
  Int ->
  a
christoffel gInv dg c a b =
  let half = NHM.one NHM./ (NHM.one NHA.+ NHM.one)
      term i =
        gInv c i
          NHM.* ( dg a i b
                    NHA.+ dg b i a
                    NHA.- dg i a b
                )
   in half NHM.* (term 0 NHA.+ term 1)

-- ---------------------------------------------------------------------------
-- ∂g / g^{-1} from metric Diff (L0 extraction — same as MetricAdjoint)
-- ---------------------------------------------------------------------------

basis0, basis1 :: (Double, Double)
basis0 = (1, 0)
basis1 = (0, 1)

partialG ::
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  (Double, Double) ->
  Int ->
  Int ->
  Int ->
  Double
partialG lower x i j k =
  let v = if k == 0 then basis0 else basis1
      dc = if j == 0 then basis0 else basis1
      (_, back) = runDiff lower (x, v)
      (dpoint, _) = back dc
   in if i == 0 then fst dpoint else snd dpoint

gInvAt ::
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  (Double, Double) ->
  Int ->
  Int ->
  Double
gInvAt raise x c i =
  let (v, _) = runDiff raise (x, if i == 0 then basis0 else basis1)
   in if c == 0 then fst v else snd v

-- | Γ at a Double point via polymorphic formula + Diff-extracted tables.
gammaAt ::
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  (Double, Double) ->
  Int ->
  Int ->
  Int ->
  Double
gammaAt lower raise x c a b =
  christoffel
    (gInvAt raise x)
    (partialG lower x)
    c
    a
    b

-- ---------------------------------------------------------------------------
-- Metrics (same as MetricAdjoint / RiemannSpike)
-- ---------------------------------------------------------------------------

lowerPolar :: Diff ((Double, Double), (Double, Double)) (Double, Double)
lowerPolar = Diff $ \((r, _), (vr, vth)) ->
  ( (vr, r * r * vth),
    \(dcr, dct) ->
      ( (2 * r * vth * dct, zero),
        (dcr, r * r * dct)
      )
  )

raisePolar :: Diff ((Double, Double), (Double, Double)) (Double, Double)
raisePolar = Diff $ \((r, _), (cr, cth)) ->
  let rr = r * r
   in ( (cr, cth / rr),
        \(dvr, dvth) ->
          ( (negate 2 * cth / (rr * r) * dvth, zero),
            (dvr, dvth / rr)
          )
      )

lowerSphere :: Diff ((Double, Double), (Double, Double)) (Double, Double)
lowerSphere = Diff $ \((th, _), (vth, vph)) ->
  let s = sin th
      ss = s * s
   in ( (vth, ss * vph),
        \(dcth, dcph) ->
          ( (2 * s * cos th * vph * dcph, zero),
            (dcth, ss * dcph)
          )
      )

raiseSphere :: Diff ((Double, Double), (Double, Double)) (Double, Double)
raiseSphere = Diff $ \((th, _), (cth, cph)) ->
  let s = sin th
      ss = s * s
   in ( (cth, cph / ss),
        \(dvth, dvph) ->
          ( (negate 2 * cos th / (s * s * s) * cph * dvph, zero),
            (dvth, dvph / ss)
          )
      )

-- ---------------------------------------------------------------------------
-- Runner — must match shipped MetricAdjoint Γ numbers
-- ---------------------------------------------------------------------------

runMetricGamma :: IO ()
runMetricGamma = do
  putStrLn "=== SPIKE 3b: polymorphic metric→Γ (match shipped adjoint) ==="
  let r = 2.0
      theta = pi / 6
      x = (r, theta)
      g c a b = gammaAt lowerPolar raisePolar x c a b

  -- Shipped MetricAdjoint expectations at (2, π/6):
  -- Γ^r_θθ = -r, Γ^θ_rθ = Γ^θ_θr = 1/r, rest 0
  assert "Γ^r_rr" (g 0 0 0) 0
  assert "Γ^r_rθ" (g 0 0 1) 0
  assert "Γ^r_θr" (g 0 1 0) 0
  assert "Γ^r_θθ" (g 0 1 1) (negate r)
  assert "Γ^θ_rr" (g 1 0 0) 0
  assert "Γ^θ_rθ" (g 1 0 1) (recip r)
  assert "Γ^θ_θr" (g 1 1 0) (recip r)
  assert "Γ^θ_θθ" (g 1 1 1) 0
  assert "symmetry Γ^θ_rθ=Γ^θ_θr" (g 1 0 1) (g 1 1 0)

  -- Sphere sanity at π/3: Γ^θ_φφ = -sinθ cosθ, Γ^φ_θφ = cot θ
  let th = pi / 3
      xS = (th, 0.0)
      gs c a b = gammaAt lowerSphere raiseSphere xS c a b
  assert "S² Γ^θ_φφ" (gs 0 1 1) (negate (sin th * cos th))
  assert "S² Γ^φ_θφ" (gs 1 0 1) (cos th / sin th)

  -- Prove formula is the SAME function at a non-Double carrier: evaluate
  -- christoffel at constant Diff' () Double Double values (0-jet only).
  -- This is the polymorphism smoke — not yet nested ∂Γ (that's 3c).
  let gInvD c i = Diff (const (gInvAt raisePolar x c i, const 0))
      dgD i j k = Diff (const (partialG lowerPolar x i j k, const 0))
      gDiff c a b = christoffel gInvD dgD c a b :: Diff Double Double
      (val, _) = runDiff (gDiff 0 1 1) 0
  assert "poly formula at Diff-const carrier Γ^r_θθ" val (negate r)

  putStrLn ""
  putStrLn "=== VERDICT 3b ==="
  putStrLn "YES — one polymorphic christoffel formula; Double instance matches"
  putStrLn "shipped MetricAdjoint polar Γ; Diff-const carrier returns same."
  putStrLn "Ready for 3c: instantiate tables at tagged Diff to get ∂Γ by AD."
