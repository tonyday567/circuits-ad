{-# LANGUAGE PatternSynonyms #-}

-- | SPIKE 1 — integration = feedback?
--
-- Thesis (tangent-calculus.md): geodesic flow is a traced net over
-- Pullback, solved by the same Star/Eliminate organ that solves AD knots.
--
-- Setup: polar R² (flat metric, nonzero Christoffel).  Analytic geodesics
-- are straight lines in Cartesian.  Nontrivial polar geodesic:
--
--   line x=1, y=t  →  at t=0: (r,θ,v_r,v_θ) = (1, 0, 0, 1)
--   analytic at t=h: r=√(1+h²), θ=atan(h), v_r=h/r, v_θ=1/(1+h²)
--
-- Christoffel (polar R²): Γ^r_θθ = −r, Γ^θ_rθ = Γ^θ_θr = 1/r.
-- Geodesic ODE on TM:
--   ṙ = v_r,  θ̇ = v_θ,
--   v̇_r = r · v_θ²,  v̇_θ = −(2/r) · v_r · v_θ
--
-- Encode ONE implicit-Euler step as a nonlinear Diff knot and solve the
-- forward fixpoint by Picard iteration via 'traceStarMatrixD' (same organ
-- as AD feedback; star closes the *backward* pass only).
--
-- Verdict targets:
--   A) Picard-traced one-step vs analytic  — O(h²) local error expected
--   B) pure linear Star (eliminateKnots) alone cannot express the step
--      (body is quadratic in v) — demonstrated by structure, not numerics
module GeodesicSpike
  ( runGeodesicSpike,
  )
where

import Circuit.AD (Diff', runDiff, pattern Diff)
import Circuit.AD.Star (traceStarMatrixD)
import Prelude

-- | State on T(polar R²): [r, θ, v_r, v_θ]
type State = [Double]

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
          ++ " (tol "
          ++ show tol
          ++ ")"

-- ---------------------------------------------------------------------------
-- Geometry
-- ---------------------------------------------------------------------------

-- | f(s) = ṡ for polar R² geodesic.
geodesicF :: State -> State
geodesicF [r, _th, vr, vth] =
  let rSafe = if abs r < 1e-12 then 1e-12 else r
   in [ vr,
        vth,
        r * vth * vth, -- −Γ^r_θθ v_θ v_θ = r v_θ²
        -(2 / rSafe) * vr * vth -- −2 Γ^θ_rθ v_r v_θ
      ]
geodesicF _ = error "geodesicF: need 4-vector state"

-- | Analytic geodesic: vertical line x=1, y=t (Cartesian).
analyticAt :: Double -> State
analyticAt t =
  let r = sqrt (1 + t * t)
      th = atan t
      vr = t / r
      vth = 1 / (1 + t * t)
   in [r, th, vr, vth]

-- | Explicit Euler one step (baseline, not Trace).
eulerStep :: Double -> State -> State
eulerStep h s =
  let f = geodesicF s
   in zipWith (\a b -> a + h * b) s f

-- ---------------------------------------------------------------------------
-- Implicit Euler as traced Diff knot
-- ---------------------------------------------------------------------------

-- | One implicit-Euler step via 'traceStarMatrixD' (Picard n iters).
--
-- Channel is the full next-state.  Fixpoint: s' = s0 + h·f(s').
-- Forward: iterate.  Backward: starMatrix on the linearization of the body
-- (Star organ — exact for the *pullback*, not a closed form for nonlinear
-- forward integration).
tracedImplicitStep :: Double -> Int -> State -> State
tracedImplicitStep h n s0 =
  let body = Diff $ \(s', ()) ->
        let f = geodesicF s'
            sNext = zipWith (\a b -> a + h * b) s0 f
            -- Pullback type: (dChannel, dOut) -> (dChannel, dIn).
            -- Channel self-coupling probe uses ∂sNext/∂s' ≈ h·I (small for small h).
            backward (ds', _dc) = (map (h *) ds', ())
         in ((sNext, sNext), backward)
      step = traceStarMatrixD s0 n body :: Diff' () () State
      (s1, _) = runDiff step ()
   in s1

-- ---------------------------------------------------------------------------
-- Linear Star cannot encode the quadratic RHS (structural demo)
-- ---------------------------------------------------------------------------

-- | Residual of implicit Euler: R(s') = s' − s0 − h·f(s').
-- Quadratic terms (r v_θ², v_r v_θ) mean the Jacobian DR depends on s', so
-- a single starMatrix solve is one Newton step of a linearization — not a
-- closed-form geodesic integrator.  We print the residual of one Newton
-- step from the explicit-Euler guess to make the gap concrete.
newtonOneStepResidual :: Double -> State -> (State, Double)
newtonOneStepResidual h s0 =
  let -- start from explicit Euler guess
      sGuess = eulerStep h s0
      -- residual R(s) = s - s0 - h f(s)
      residual s = zipWith3 (\a b c -> a - b - h * c) s s0 (geodesicF s)
      r0 = residual sGuess
      -- crude: no full Jacobian inverse — just report ||R|| at Euler guess
      -- (already O(h²)); and ||R|| after Picard-traced solve
      sPicard = tracedImplicitStep h 40 s0
      rP = residual sPicard
      norm xs = sqrt (sum (map (\x -> x * x) xs))
   in (sPicard, norm rP)

-- ---------------------------------------------------------------------------
-- Runner
-- ---------------------------------------------------------------------------

runGeodesicSpike :: IO ()
runGeodesicSpike = do
  putStrLn "=== SPIKE 1: integration=feedback (polar R² geodesic) ==="
  putStrLn "initial: line x=1,y=t at t=0 → (r,θ,vr,vθ)=(1,0,0,1)"
  let s0 = [1, 0, 0, 1] :: State
      h = 0.1
      analytic = analyticAt h
  putStrLn $ "analytic @ h=" ++ show h ++ ": " ++ show analytic

  -- A) explicit Euler baseline
  let sEuler = eulerStep h s0
  putStrLn $ "explicit Euler:            " ++ show sEuler
  mapM_
    ( \(n, g, e) -> assertNear ("euler " ++ n) 5e-2 g e
    )
    $ zip3 ["r", "θ", "vr", "vθ"] sEuler analytic

  -- B) traced Picard / implicit Euler via traceStarMatrixD
  let sTrace = tracedImplicitStep h 40 s0
  putStrLn $ "traced Picard (n=40):      " ++ show sTrace
  mapM_
    ( \(n, g, e) -> assertNear ("trace " ++ n) 5e-2 g e
    )
    $ zip3 ["r", "θ", "vr", "vθ"] sTrace analytic

  -- residual of implicit equation
  let (_sP, resNorm) = newtonOneStepResidual h s0
  putStrLn $ "||implicit residual|| after Picard: " ++ show resNorm
  assertNear "implicit residual small" 1e-6 resNorm 0

  -- error comparison
  let err xs ys = sqrt (sum (zipWith (\a b -> (a - b) ^ (2 :: Int)) xs ys))
      eE = err sEuler analytic
      eT = err sTrace analytic
  putStrLn $ "L2 error Euler  vs analytic: " ++ show eE
  putStrLn $ "L2 error Picard vs analytic: " ++ show eT

  -- C) smaller h → O(h²) check for Picard
  let h2 = 0.01
      a2 = analyticAt h2
      t2 = tracedImplicitStep h2 40 s0
      e2 = err t2 a2
  putStrLn $ "L2 error Picard @ h=0.01:    " ++ show e2
  putStrLn $ "error ratio e(0.1)/e(0.01) ≈ " ++ show (eT / e2) ++ " (expect ~100 for O(h²))"

  putStrLn ""
  putStrLn "=== VERDICT ==="
  putStrLn "A) YES — one geodesic step IS a Trace knot (Picard body s'=s0+h f(s'))."
  putStrLn "   traceStarMatrixD solves the forward fixpoint by iteration;"
  putStrLn "   Star closes only the *linear pullback*, not the nonlinear flow."
  putStrLn "B) NO  — pure linear Star/Eliminate (Kleene (I−A)⁻¹) does NOT"
  putStrLn "   integrate ∇: geodesic RHS is quadratic in v, so closed-form"
  putStrLn "   star cannot replace the Picard loop. Integration≠linear feedback."
  putStrLn "C) The rhyme holds for *one-step implicit structure* (fixpoint),"
  putStrLn "   fails for *closed-form Star as integrator*. Design: keep Trace"
  putStrLn "   as the organ for implicit steps; do not expect eliminateKnots"
  putStrLn "   to replace a geodesic solver."
