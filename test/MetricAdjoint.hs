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
--     @g = diag(1, r^2)@, so @g@ is represented as a 'Diff'.  The metric's
--     pullback carries @∂g@ in its point-slot; currently that derivative is
--     hand-coded in each metric, with nested AD as the future honest source.
--
-- This module keeps the spike small: one combinator, two metric instances
-- (Euclidean and polar), and two executable oracles.
module MetricAdjoint
  ( runMetricAdjointTests,
  )
where

import Circuit.AD
import Circuit.AD.Metric (adjointWith)
import NumHask.Prelude
import Prelude ()

-- | Basis vectors in R^2.
basis0 :: (Double, Double)
basis0 = (1, 0)

basis1 :: (Double, Double)
basis1 = (0, 1)

-- | Extract the partial derivatives of the metric components from the metric's
-- own AD pullback.  For a lower operation @c_j = g_{jk}(x) v^k@, the pullback's
-- point-slot at @v = e_k@ and output cotangent @dc = e_j@ yields the covector
-- @∂_i g_{jk} dx^i@.  Probing all four combinations assembles @∂g@.
partialG ::
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  (Double, Double) ->
  -- | @∂_i g_{jk}@ indexed by @(i, j, k)@.
  (((Double, Double), (Double, Double)), ((Double, Double), (Double, Double)))
partialG lower x =
  let probe v dc =
        let (_, back) = runDiff lower (x, v)
            (dpoint, _) = back dc
         in dpoint
      -- ∂_i g_{j0} for i,j = 0,1
      row0 = (probe basis0 basis0, probe basis0 basis1)
      -- ∂_i g_{j1} for i,j = 0,1
      row1 = (probe basis1 basis0, probe basis1 basis1)
   in (row0, row1)

-- | Christoffel symbols @Γ^c_{ab}@ of a 2D metric, from @∂g@ and @g^{-1}@.
--
-- Uses the standard formula @Γ^c_{ab} = ½ g^{ci}(∂_a g_{ib} + ∂_b g_{ia} - ∂_i g_{ab})@.
christoffel2D ::
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  (Double, Double) ->
  -- | @(Γ^0_{00}, Γ^0_{01}, Γ^0_{10}, Γ^0_{11}, Γ^1_{00}, Γ^1_{01}, Γ^1_{10}, Γ^1_{11})@.
  (Double, Double, Double, Double, Double, Double, Double, Double)
christoffel2D lower raise x =
  let pg = partialG lower x
      -- g^{c i} for i = 0,1; c = 0,1
      ((g00, g01), (g10, g11)) =
        let (v0, _) = runDiff raise (x, basis0)
            (v1, _) = runDiff raise (x, basis1)
         in (v0, v1)
      -- ∂_i g_{jk} accessor
      d :: Int -> Int -> Int -> Double
      d i j k = case (i, j, k) of
        (0, 0, 0) -> fst (fst (fst pg))
        (0, 0, 1) -> fst (snd (fst pg))
        (0, 1, 0) -> fst (fst (snd pg))
        (0, 1, 1) -> fst (snd (snd pg))
        (1, 0, 0) -> snd (fst (fst pg))
        (1, 0, 1) -> snd (snd (fst pg))
        (1, 1, 0) -> snd (fst (snd pg))
        (1, 1, 1) -> snd (snd (snd pg))
        _ -> error "christoffel2D: index out of range"
      gamma :: Int -> Int -> Int -> Double
      gamma c a b =
        0.5
          * ( (if c == (0 :: Int) then g00 else g10)
                * (d a 0 b + d b 0 a - d 0 a b)
                + (if c == (0 :: Int) then g01 else g11)
                * (d a 1 b + d b 1 a - d 1 a b)
            )
   in ( gamma 0 0 0,
        gamma 0 0 1,
        gamma 0 1 0,
        gamma 0 1 1,
        gamma 1 0 0,
        gamma 1 0 1,
        gamma 1 1 0,
        gamma 1 1 1
      )

-- | Directional derivative of a vector field from its AD pullback.
--
-- For @V : R^2 -> R^2@, the Jacobian @J_V@ is recovered from the pullback
-- @J_V^T@ by @e_c · (J_V dx) = dx · (J_V^T e_c)@.
directionalDerivative ::
  Diff (Double, Double) (Double, Double) ->
  (Double, Double) ->
  (Double, Double) ->
  (Double, Double)
directionalDerivative v x dx =
  let (_, vt) = runDiff v x
      vTe0 = vt basis0
      vTe1 = vt basis1
   in (fst dx * fst vTe0 + snd dx * snd vTe0, fst dx * fst vTe1 + snd dx * snd vTe1)

-- | Covariant derivative @∇_dx V@ at a point, using the metric's Christoffel
-- symbols: @∇_dx V = ∂_dx V + Γ(x)(dx, V(x))@.
covariantDerivative ::
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  Diff ((Double, Double), (Double, Double)) (Double, Double) ->
  Diff (Double, Double) (Double, Double) ->
  (Double, Double) ->
  (Double, Double) ->
  (Double, Double)
covariantDerivative lower raise v x dx =
  let (vx, _) = runDiff v x
      (g000, g001, g010, g011, g100, g101, g110, g111) = christoffel2D lower raise x
      dx0 = fst dx
      dx1 = snd dx
      v0 = fst vx
      v1 = snd vx
      gamma0 = g000 * dx0 * v0 + g001 * dx0 * v1 + g010 * dx1 * v0 + g011 * dx1 * v1
      gamma1 = g100 * dx0 * v0 + g101 * dx0 * v1 + g110 * dx1 * v0 + g111 * dx1 * v1
      partial = directionalDerivative v x dx
   in (fst partial + gamma0, snd partial + gamma1)

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

  putStrLn "metric adjoint: Christoffel symbols from metric pullbacks"
  let (g000, g001, g010, g011, g100, g101, g110, g111) = christoffel2D lowerPolar raisePolar (r, theta)
  -- Polar metric: Γ^r_{θθ} = -r, Γ^θ_{rθ} = Γ^θ_{θr} = 1/r, all others zero.
  assert "Γ^r_{rr}" g000 0
  assert "Γ^r_{rθ}" g001 0
  assert "Γ^r_{θr}" g010 0
  assert "Γ^r_{θθ}" g011 (negate r)
  assert "Γ^θ_{rr}" g100 0
  assert "Γ^θ_{rθ}" g101 (recip r)
  assert "Γ^θ_{θr}" g110 (recip r)
  assert "Γ^θ_{θθ}" g111 0
  assert "symmetry Γ^θ_{rθ} = Γ^θ_{θr}" g101 g110

  putStrLn "metric adjoint: covariant derivative ∇ = ∂ + Γ"
  -- Polar basis vector e_r as a constant vector field: V(r,θ) = (1,0).
  let eR = Diff $ const ((1, 0), const (0, 0))
      -- ∇_θ e_r = (0, 1/r)
      nablaThetaER = covariantDerivative lowerPolar raisePolar eR (r, theta) basis1
  assertV2 "∇_θ e_r" nablaThetaER (0, recip r)

  -- ∇_θ e_θ = (-r, 0)
  let eTheta = Diff $ const ((0, 1), const (0, 0))
      nablaThetaTheta = covariantDerivative lowerPolar raisePolar eTheta (r, theta) basis1
  assertV2 "∇_θ e_θ" nablaThetaTheta (negate r, 0)
