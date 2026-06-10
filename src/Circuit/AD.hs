{-# LANGUAGE CPP #-}

-- | Reverse-mode automatic differentiation via a lens-shaped base arrow.
--
-- 'D' is a differentiable function @a -> b@ that carries its own pullback:
-- given a cotangent @db@ on the output, produce a cotangent @da@ on the input.
-- This is the same shape as Conal Elliott's \"Simple Essence of AD\" reverse
-- mode, lifted into a 'Category' so it can be used as the base arrow for
-- 'Circuit'.
--
-- With the 'Trace' @(,)@ instance, 'reify' \"Circuit D\" runs forward and
-- pulls back — reverse-mode AD with no GADT changes.  The backward pass
-- through a 'Knot' uses a lazy fixpoint (the implicit function theorem):
-- the gradient at a fixed point solves its own affine equation.
--
-- = Example
--
-- Differentiating @x²@ through a circuit:
--
-- >>> import Circuit (Circuit(..), reify)
-- >>> import Circuit.AD
-- >>> import Prelude hiding (id, (.))
-- >>> let f = Lift (D (\x -> (x * x, \dx' -> 2 * x * dx'))) :: Circuit D (,) Double Double
-- >>> let (y, pullback) = runD (reify f) 3.0
-- >>> y
-- 9.0
-- >>> pullback 1.0
-- 6.0
module Circuit.AD
  ( -- * Differentiable arrow
    D (..),

    -- * Trace variants
    traceNFrom,
  )
where

#ifdef __GLASGOW_HASKELL__
import Control.Category
#else
import Circuit.Classes
#endif

import Circuit.Additive (Additive (..))
import Circuit.Traced (Trace (..))
import Prelude hiding (id, (.))

-- $setup
-- >>> import Circuit (Circuit (..), reify)
-- >>> import Prelude hiding (id, (.))

-- | A reverse-mode differentiable function.
--
-- @runD f a@ returns a pair @(b, pullback)@ where @b = f a@ and @pullback@
-- maps a cotangent @db@ on the output to a cotangent @da@ on the input.
newtype D a b = D
  { -- | Run the forward pass and return the backward pullback.
    runD :: a -> (b, b -> a)
  }

instance Category D where
  id = D (\a -> (a, id))
  D f . D g = D $ \a ->
    let (b, gb) = g a
        (c, fc) = f b
     in (c, gb . fc)

-- | 'Trace' for 'D' with the @(,)@ tensor.
--
-- The forward pass ties the standard lazy knot:
--
-- @
-- let (a, c) = body (a, b) in c
-- @
--
-- The backward pass ties the /same shape/ of knot, transposed.  Given @dc@
-- on the output, the full backward pair @(da, db)@ satisfies a self-referential
-- equation solved by a single lazy binding:
--
-- @
-- let bd = backward (fst bd, dc) in snd bd
-- @
--
-- The knot flows through the /pair/ rather than through the channel cotangent
-- alone — 'backward' is called once, the pair is destructured once, and the
-- shape mirrors the forward knot identically.
--
-- 'pullback' closes over 'backward', which closes over the forward pass's
-- intermediates.  The closure is the tape: no explicit Wengert list is built
-- because GHC's heap holds the graph.  For linear backward maps this is a
-- Neumann series computed lazily; for general maps it is the implicit function
-- theorem as a lazy knot.
instance Trace D (,) where
  trace (D body) = D $ \b ->
    let -- Forward: standard lazy knot
        ~((a, c), backward) = body (a, b)
        -- Backward: same shape, transposed — knot through the pair
        pullback dc =
          let bd = backward (fst bd, dc)
           in snd bd
     in (c, pullback)

  untrace (D f) = D $ \(a, b) ->
    let (c, back) = f b
     in ((a, c), \(da, dc) -> (da, back dc))

-- | Iterated trace for strict carriers.
--
-- The lazy 'trace' diverges on strict cotangent types ('Double', etc.) when
-- the feedback channel has nonzero self-coupling (@∂a_out\/∂a_in ≠ 0@).
-- 'traceNFrom' replaces the lazy knot with truncated fixed-point iteration.
--
--   * __Forward__ — iterate from caller-supplied seed @x0@, N steps.
--     There is no canonical seed for the forward pass (the fixpoint is
--     arbitrary nonlinear), so the caller provides one.
--
--   * __Backward__ — iterate from 'zero', N steps, extract 'snd' once.
--     The backward equation is guaranteed affine (calculus promises
--     linearity in cotangents), so 'zero' is the principled seed.
--     The Neumann summation happens /inside/ the iteration — no
--     double-counting, and 'plus' retreats to where the theory says
--     it lives: inside prims and 'Copy'.
--
-- Lives beside the lawful-but-lazy instance, not replacing it.
traceNFrom ::
  Additive (->) a =>
  a ->
  Int ->
  D (a, b) (a, c) ->
  D b c
traceNFrom x0 n (D body) = D $ \b ->
  let -- Forward: iterate from caller-supplied seed
      stepFwd x = let ((x', _), _) = body (x, b) in x'
      a = iterate stepFwd x0 !! n
      ((_, c), backward) = body (a, b)
      -- Backward: iterate from zero, extract result once
      pullback dc =
        let stepBwd d = fst (backward (d, dc))
            da = iterate stepBwd (zero ()) !! n
         in snd (backward (da, dc))
   in (c, pullback)
