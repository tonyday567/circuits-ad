{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TupleSections #-}

-- | Metric-aware adjoint spike.
--
-- A metric-aware transpose (the adjoint of @J : a -> b@) is
-- @g_a^-1 . J^T . g_b@, where @g_a@ and @g_b@ are the metrics on the domain
-- and codomain.  The key design observations are:
--
--   * two metrics, not one — domain and codomain each carry their own @g@;
--   * conjugate only at the boundary — composition of adjoints is free because
--     the intermediate metrics cancel;
--   * @g@ is a field, not a matrix — the first interesting instance is polar
--     @g = diag(1, r^2)@, so @g@ is represented as a 'Diff' and AD gives
--     @∂g@ for free when we later need Christoffel symbols.
--
-- This module keeps the spike small: one combinator, two metric instances
-- (Euclidean and polar), and two executable oracles.
module MetricAdjoint
  ( runMetricAdjointTests,
  )
where

import Circuit.AD
import NumHask.Prelude
import Prelude ()

near :: Double -> Double -> Bool
near x y = abs (x - y) < 1e-9

assert :: String -> Double -> Double -> IO ()
assert name got expected =
  if near got expected
    then putStrLn $ "  PASS " ++ name ++ ": " ++ show got
    else do
      putStrLn $ "  FAIL " ++ name ++ ": got " ++ show got ++ ", expected " ++ show expected
      error "metric adjoint test failed"

assertV2 :: String -> (Double, Double) -> (Double, Double) -> IO ()
assertV2 name (x, y) (x', y') = do
  assert (name ++ " fst") x x'
  assert (name ++ " snd") y y'

-- | Adjoint of a 'Diff' with respect to domain and codomain metrics.
--
-- The metric operations are themselves 'Diff's of type @Diff (point, vector)
-- vector@: the forward pass lowers or raises a vector at the given point.
-- We use only the forward pass for the adjoint; the fact that @g@ is a 'Diff'
-- means its derivative is available automatically when we move on to @∇@.
adjointWith ::
  -- | @g_a^-1@ — raise a covector on the domain to a vector
  Diff (a, a) a ->
  -- | @g_b@ — lower a vector on the codomain to a covector
  Diff (b, b) b ->
  -- | @J : a -> b@
  Diff a b ->
  -- | @J@ with its pullback conjugated to the @g@-adjoint.  The type is still
  -- @Diff a b@ because the lens stores the forward map @a -> b@ and the
  -- backward map @b -> a@; the adjoint lives in the pullback.
  Diff a b
adjointWith raiseA lowerB (Diff f) = Diff $ \x ->
  let (y, jt) = f x
   in ( y,
        \db ->
          let (lowered, _) = runDiff lowerB (y, db)
              covectorA = jt lowered
              (raised, _) = runDiff raiseA (x, covectorA)
           in raised
      )

-- | Euclidean metric @g = δ@ on @R@: lower and raise are both the identity.
euclidean1D :: Diff (Double, Double) Double
euclidean1D = Diff $ \(_, v) -> (v, (0,))

-- | Euclidean metric @g = δ@ on @R^2@: lower and raise are both the identity.
euclidean2D :: Diff ((Double, Double), (Double, Double)) (Double, Double)
euclidean2D = Diff $ \(_, v) -> (v, ((0, 0),))

-- | Polar metric @g = diag(1, r^2)@ in coordinates @(r, θ)@.
--
-- Lower: @(v_r, v_θ) ↦ (v_r, r^2 v_θ)@.
-- Raise: @(c_r, c_θ) ↦ (c_r, c_θ / r^2)@.
lowerPolar :: Diff ((Double, Double), (Double, Double)) (Double, Double)
lowerPolar = Diff $ \((r, _), (vr, vtheta)) ->
  ( (vr, r * r * vtheta),
    \(dcr, dctheta) ->
      ( (2 * r * vtheta * dctheta, zero),
        (dcr, r * r * dctheta)
      )
  )

raisePolar :: Diff ((Double, Double), (Double, Double)) (Double, Double)
raisePolar = Diff $ \((r, _), (cr, ctheta)) ->
  let rr = r * r
   in ( (cr, ctheta / rr),
        \(dv_r, dv_theta) ->
          ( (negate 2 * ctheta / (rr * r) * dv_theta, zero),
            (dv_r, dv_theta / rr)
          )
      )

-- | A simple nonlinear map @(r, θ) -> r^2 cos θ@ used for the polar oracle.
fPolar :: Diff (Double, Double) Double
fPolar = Diff $ \(r, theta) ->
  let val = r * r * cos theta
   in ( val,
        \d -> (2 * r * d * cos theta, negate (r * r * d * sin theta))
      )

-- | Conversion from polar coordinates to cartesian coordinates.
polarToCart :: Diff (Double, Double) (Double, Double)
polarToCart = Diff $ \(r, theta) ->
  let x = r * cos theta
      y = r * sin theta
   in ( (x, y),
        \(dx, dy) ->
          ( dx * cos theta + dy * sin theta,
            negate dx * r * sin theta + dy * r * cos theta
          )
      )

-- | Euclidean gradient of @fPolar ∘ cartToPolar@, expressed in cartesian
-- coordinates.  This is the reference for the polar oracle.
fCart :: Diff (Double, Double) Double
fCart = Diff $ \(x, y) ->
  let r = sqrt (x * x + y * y)
      val = x * r
      dx = r + x * x / r
      dy = x * y / r
   in (val, \d -> (d * dx, d * dy))

runMetricAdjointTests :: IO ()
runMetricAdjointTests = do
  putStrLn "metric adjoint: δ-regression"
  let j = Diff $ \(x, y) -> ((x + y, x - y), \(du, dv) -> (du + dv, du - dv))
      (_, pbEuc) = runDiff (adjointWith euclidean2D euclidean2D j) (1.0, 2.0)
      (_, pbPlain) = runDiff j (1.0, 2.0)
  assertV2 "euclidean adjoint equals plain transpose" (pbEuc (1.0, 0.0)) (pbPlain (1.0, 0.0))

  putStrLn "metric adjoint: polar gradient oracle"
  let r = 2.0
      theta = pi / 6
      (_, pbPolar) = runDiff (adjointWith raisePolar euclidean1D fPolar) (r, theta)
      polarGrad = pbPolar 1.0
      -- Reference: polar gradient is (∂f/∂r, (1/r^2) ∂f/∂θ)
      expectedPolar = (2 * r * cos theta, negate (sin theta))
  assertV2 "polar gradient matches analytic" polarGrad expectedPolar

  -- Convert the polar gradient vector to cartesian coordinates using the
  -- Jacobian @∂(x,y)/∂(r,θ)@.  The Diff pullback gives us @J^T@, so the i-th
  -- component of @J v@ is @v · (J^T e_i)@.
  let (_, jt) = runDiff polarToCart (r, theta)
      jTe1 = jt (1, 0)
      jTe2 = jt (0, 1)
      polarGradInCart = (fst polarGrad * fst jTe1 + snd polarGrad * snd jTe1, fst polarGrad * fst jTe2 + snd polarGrad * snd jTe2)
      (_, eucGrad) = runDiff fCart (r * cos theta, r * sin theta)
  assertV2 "polar gradient pushed to cartesian equals euclidean gradient" polarGradInCart (eucGrad 1.0)

  putStrLn "metric adjoint: polar raise/lower round-trip"
  let v = (1.5, negate 0.75)
      (vLowered, _) = runDiff lowerPolar ((r, theta), v)
      (vRoundTrip, _) = runDiff raisePolar ((r, theta), vLowered)
  assertV2 "raisePolar . lowerPolar = id" vRoundTrip v

  putStrLn "metric adjoint: compositionality"
  -- fPolar = fCart . polarToCart, so the metric adjoint should satisfy
  -- adjointWith gA gC (j2 . j1) = adjointWith gB gC j2 . adjointWith gA gB j1
  let left = adjointWith raisePolar euclidean1D (fCart . polarToCart)
      right = adjointWith euclidean2D euclidean1D fCart . adjointWith raisePolar euclidean2D polarToCart
      (_, pbLeft) = runDiff left (r, theta)
      (_, pbRight) = runDiff right (r, theta)
  assertV2 "adjoint distributes over composition" (pbLeft 1.0) (pbRight 1.0)
