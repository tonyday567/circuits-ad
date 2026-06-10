-- | Oracle tests: circuits reverse-mode AD against ad-delcont.
--
-- Three claims, falsifiable by property test:
--
-- 1. __Primitive agreement__ — @reify \@D@ matches @rad1@ on the same
--    primitive set.
-- 2. __Triangle identity__ — @lower . encode \@D = reify \@D@, and both
--    match ad-delcont.
-- 3. __Knot differentiation__ — @traceNFrom \@D@ differentiates through a
--    fixed-point loop.
--
-- /Stage 2 gap/: the quadratic test (@ax²+bx+c@) is not expressible in
-- Stage 1.  It requires 'Copy' (use @x@ twice) and 'Add' (sum the
-- contributions) — the bimonoid rows in 'Circuit.Net'.
--
-- Run with @cabal-docspec@ from the package root.
module Circuit.AD.Oracle
  ( -- * Test functions (exported for doctest)
    sqr,
    sinSqr,
    sqrtBody,
  )
where

import Control.Category ((>>>))
import Circuit (Circuit (..), reify)
import Circuit.AD (D (..), traceNFrom)
import Numeric.AD.DelCont (rad1)
import Prelude hiding (id, (.))

-- $setup
-- >>> 1 + 1 :: Int
-- 2
-- >>> import Control.Category ((>>>))
-- >>> import Circuit (Circuit(..), reify)
-- >>> import Circuit.AD (D(..), traceNFrom)
-- >>> import Numeric.AD.DelCont (rad1)
-- >>> import Prelude hiding (id, (.))

-- ---------------------------------------------------------------------------
-- Shared primitives
-- ---------------------------------------------------------------------------

-- | Pure function: @x -> x * x@.
sqr :: Num a => a -> a
sqr x = x * x

-- | Pure function: @x -> sin (x * x)@.
sinSqr :: Floating a => a -> a
sinSqr x = sin (x * x)

-- ===========================================================================
-- Test 1: Primitive agreement — reify @D vs rad1
-- ===========================================================================

-- | @x²@ as a Circuit D.
sqrCircuit :: Circuit D (,) Double Double
sqrCircuit = Lift (D (\x -> (x * x, \dx -> 2 * x * dx)))

-- | @sin(x²)@ as two composed Lift Ds.
sinSqrCircuit :: Circuit D (,) Double Double
sinSqrCircuit =
  Lift (D (\x -> (x * x, \dx -> 2 * x * dx)))
    >>> Lift (D (\x -> (sin x, \dx -> cos x * dx)))

-- | Derivative of @x²@ agrees: @reify @D@ vs @rad1@.
--
-- >>> let test x = let (yc, pb) = runD (reify sqrCircuit) x; (ya, ga) = rad1 sqr x in abs (yc - ya) < 1e-10 && abs (pb 1.0 - ga) < 1e-10
-- >>> all test [-2.0, -1.0, 0.0, 0.5, 1.0, 2.5, 10.0]
-- True

-- | Derivative of @sin(x²)@ agrees: composition of two Ds vs @rad1@.
--
-- >>> let test x = let (yc, pb) = runD (reify sinSqrCircuit) x; (ya, ga) = rad1 sinSqr x in abs (yc - ya) < 1e-10 && abs (pb 1.0 - ga) < 1e-10
-- >>> all test [0.1, 0.5, 1.0]
-- True

-- ===========================================================================
-- Test 2: Triangle identity — lower . encode = reify
-- ===========================================================================

-- | The triangle holds on a simple D circuit.
--
-- >>> import Circuit (encode, lower)
-- >>> let circuit = sqrCircuit
-- >>> let (yr, pb) = runD (reify circuit) 3.0
-- >>> let (ye, pbe) = lower (encode circuit) 3.0
-- >>> abs (yr - ye) < 1e-10 && abs (pb 1.0 - pbe 1.0) < 1e-10
-- True

-- | The triangle holds on a composed D circuit.
--
-- >>> import Circuit (encode, lower)
-- >>> let circuit = sinSqrCircuit
-- >>> let test x = let (yr, pb) = runD (reify circuit) x; (ye, pbe) = lower (encode circuit) x in abs (yr - ye) < 1e-10 && abs (pb 1.0 - pbe 1.0) < 1e-10
-- >>> all test [0.1, 0.5, 1.0, 2.0]
-- True

-- ===========================================================================
-- Test 3: Knot differentiation — traceNFrom @D
-- ===========================================================================

-- | Square root by Babylonian iteration:
--   @x_{n+1} = (x_n + a\/x_n) \/ 2@.
--
-- The forward value @x'@ fans out to both the channel and the output
-- (a Copy), so the backward pass fans in the two cotangents via @+@
-- (an Add).  The channel Jacobian @jx = (1 − a\/x²)\/2@ vanishes at
-- the fixed point — Newton's quadratic convergence.
--
-- At the fixed point, the backward affine fixpoint @dx = (dx+dout)*jx@
-- collapses to @dx = 0@, and the gradient flows purely through
-- @ja = 1\/(2x) = 0.125@ at @x = 4, a = 16@.
sqrtBody :: D (Double, Double) (Double, Double)
sqrtBody = D $ \(x, a) ->
  let x' = (x + a / x) / 2
      jx = (1 - a / (x * x)) / 2   -- ∂x'/∂x: vanishes at x = √a
      ja = 1 / (2 * x)             -- ∂x'/∂a
   in ( (x', x')                    -- Copy: to channel AND output
      , \(dx, dout) ->
          let d = dx + dout         -- Add: fan-in on the contravariant side
           in (d * jx, d * ja) )

-- | traceNFrom forward pass converges to @sqrt(a)@.
--
-- >>> let (yn, _) = runD (traceNFrom 8.0 20 sqrtBody) 16.0
-- >>> abs (yn - 4.0) < 1e-10
-- True

-- | traceNFrom gradient matches @1\/(2√a) = 0.125@.
--
-- The Neumann series is one term long — at the fixed point @jx = 0@,
-- so only the @ja@ path contributes.
--
-- >>> let (_, pbn) = runD (traceNFrom 8.0 20 sqrtBody) 16.0
-- >>> abs (pbn 1.0 - 0.125) < 1e-10
-- True
