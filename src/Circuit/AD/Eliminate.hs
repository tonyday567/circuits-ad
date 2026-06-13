{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Star-elimination of @(,)@ knots in linear 'Pullback' nets.
--
-- A 'Net Pullback (,)' built by 'Circuit.AD.linearizeNet' is linear by
-- construction: every 'Lift' is a pointwise pullback, every 'Compose' is
-- function composition, and every 'Knot' ties an affine feedback equation.
-- This module eliminates those knots in closed form using the Kleene star
-- ('NumHask.Algebra.Ring.StarSemiring' for scalar channels,
-- 'Hasknum.Matrix.starMatrix' for vector channels).
--
-- The resulting net has no 'Knot' constructors, so it can be evaluated on
-- strict carriers without the lazy-knot divergence that 'Trace Pullback (,)'
-- suffers when channel self-coupling is non-zero.
module Circuit.AD.Eliminate
  ( -- * Channel abstraction
    StarChannel (..),

    -- * Knot elimination
    eliminateKnots,
  )
where

import Circuit.Additive (Additive (..))
import Circuit.AD.Melt (melt)
import Circuit.AD.Pullback (Pullback (..))
import Circuit.Dup (Dup (..))
import Circuit.Monoidal (MonoidalP (..))
import Circuit.Net (Net (..))
import Control.Category (Category (..))
import Data.Proxy (Proxy (..))
import Hasknum.Matrix (FieldStar (..), Matrix (..), matVec, starMatrix)
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import Prelude hiding (id, (.))
import Prelude qualified as P
import Unsafe.Coerce (unsafeCoerce)

-- | Feedback channels that support star-elimination.
--
-- The class abstracts over scalar and vector channels.  For a scalar channel
-- the self-coupling is a single scalar; for a vector channel it is a matrix.
class
  ( NHR.StarSemiring (Scalar j),
    NHA.Additive (Scalar j),
    NHM.Multiplicative (Scalar j)
  ) =>
  StarChannel j
  where
  -- | The scalar carrier of the channel (e.g. 'FieldStar' or the element
  -- type of a list).
  type Scalar j

  -- | Dimension of the channel cotangent space.
  channelDim :: j -> Int

  -- | Zero channel cotangent of the given dimension.
  zeroChannel :: Int -> j

  -- | Basis vector @e_i@ of the given dimension.
  basisChannel :: Int -> Int -> j

  -- | Build the self-coupling matrix of a linear map @j -> j@ by probing
  -- each basis vector.
  selfMatrix :: (j -> j) -> Matrix (Scalar j)

  -- | Apply a matrix to a channel cotangent.
  applyMatrix :: Matrix (Scalar j) -> j -> j

  -- | Additive inverse of a channel cotangent.
  negateChannel :: j -> j

-- | One-dimensional channel over a 'StarSemiring' scalar.
instance StarChannel FieldStar where
  type Scalar FieldStar = FieldStar
  channelDim _ = 1
  zeroChannel _ = NHA.zero
  basisChannel _ _ = NHM.one
  selfMatrix f = Matrix [[f NHM.one]]
  applyMatrix (Matrix [[s]]) v = s NHM.* v
  applyMatrix _ _ = error "Circuit.AD.Eliminate.applyMatrix: scalar channel expected a 1x1 matrix"
  negateChannel (FieldStar x) = FieldStar (P.negate x)

-- | n-dimensional channel as a list of scalar cotangents.
instance
  ( NHR.StarSemiring a,
    NHA.Additive a,
    NHA.Subtractive a,
    NHM.Multiplicative a
  ) =>
  StarChannel [a]
  where
  type Scalar [a] = a
  channelDim = length
  zeroChannel n = replicate n NHA.zero
  basisChannel n i = [if k == i then NHM.one else NHA.zero | k <- [0 .. n - 1]]
  selfMatrix f =
    let n = channelDim (f [])
        cols = [f (basisChannel n i) | i <- [0 .. n - 1]]
     in Matrix [[col !! k | col <- cols] | k <- [0 .. n - 1]]
  applyMatrix = matVec
  negateChannel = fmap NHA.negate

-- | 'FieldStar' is a numeric carrier, so it can be the additive monoid used
-- by structural rows when they appear inside an eliminable net.
instance Additive (->) FieldStar where
  plus (FieldStar x, FieldStar y) = FieldStar (x P.+ y)
  zero _ = FieldStar 0

-- | A cotangent arrow that carries the same information as 'Pullback' but is
-- tagged so that its 'Knot' nodes can be solved by the Kleene star.
newtype StarPullback b a = StarPullback
  { runStarPullback :: b -> a
  }

instance Category StarPullback where
  id = StarPullback id
  StarPullback g . StarPullback f = StarPullback (g . f)

instance MonoidalP StarPullback where
  parA (StarPullback f) (StarPullback g) =
    StarPullback (\(a, c) -> (f a, g c))
  swapA = StarPullback (\(a, b) -> (b, a))

-- | Structural fan-out / fan-in on 'StarPullback'.
instance Additive (->) a => Dup StarPullback a where
  dup = StarPullback (\a -> (a, a))
  discard = StarPullback (\_ -> ())

-- | Addition and zero on 'StarPullback'.
instance Additive (->) a => Additive StarPullback a where
  plus = StarPullback (\(a, b) -> plus (a, b))
  zero = StarPullback (\_ -> zero ())

-- | Solve an affine @(,)@ knot in closed form.
--
-- For a knot body @f :: (j, c) -> (j, b)@, the channel self-coupling @A@
-- satisfies @dx = A·dx + C·dc@, whose solution is @dx = star A · C·dc@.
-- The traced arrow returns @db@ directly.
traceStarPullback ::
  (StarChannel j, Additive (->) j) =>
  StarPullback (j, c) (j, b) ->
  StarPullback c b
traceStarPullback (StarPullback body) = StarPullback $ \dc ->
  let zeroJ0 = zeroChannel 0
      cdc = fst (body (zeroJ0, dc))
      aMat =
        selfMatrix
          ( \dj ->
              plus
                (fst (body (dj, dc)), negateChannel (fst (body (zeroJ0, dc))))
          )
      da = applyMatrix (starMatrix aMat) cdc
   in snd (body (da, dc))

-- | Eliminate all @(,)@ knots in a linear pullback net.
--
-- The channel type is passed explicitly because it is existentially
-- quantified inside 'Knot'.  In nets produced by 'linearizeNet' all knots
-- share the same channel, so 'unsafeCoerce' is safe: it only reveals the
-- channel type that the caller already knows.
eliminateKnots ::
  (StarChannel j, Additive (->) j) =>
  Proxy j ->
  Net Pullback (,) b a ->
  Net Pullback (,) b a
eliminateKnots proxy n =
  Lift (Pullback (runStarPullback (runStarNet proxy (toStar (melt n)))))

-- | Re-interpret a 'Pullback' net as a 'StarPullback' net, preserving all
-- structure.
toStar :: Net Pullback (,) b a -> Net StarPullback (,) b a
toStar = \case
  Lift p -> Lift (StarPullback (runPullback p))
  Compose g f -> Compose (toStar g) (toStar f)
  Par f g -> Par (toStar f) (toStar g)
  Swap -> Swap
  Knot f -> Knot (toStar f)
  Copy -> unsupported "Copy"
  Discard -> unsupported "Discard"
  Add -> unsupported "Add"
  Zero -> unsupported "Zero"
  where
    unsupported name =
      error $
        "Circuit.AD.Eliminate.toStar: structural "
          ++ name
          ++ " nodes are not supported; fuse them into Lifts first"

-- | Interpret a 'StarPullback' net, solving every 'Knot' in closed form.
--
-- The channel type @j@ is fixed at the top level; each 'Knot' is coerced to
-- use that channel.  This is safe for uniform-channel nets such as those
-- produced by 'linearizeNet'.
runStarNet ::
  (StarChannel j, Additive (->) j) =>
  Proxy j ->
  Net StarPullback (,) b a ->
  StarPullback b a
runStarNet proxy = \case
  Lift p -> p
  Compose g f -> runStarNet proxy g . runStarNet proxy f
  Par f g -> parA (runStarNet proxy f) (runStarNet proxy g)
  Swap -> swapA
  Knot f -> solveKnot proxy (unsafeCoerce f)
  Copy -> unsupported "Copy"
  Discard -> unsupported "Discard"
  Add -> unsupported "Add"
  Zero -> unsupported "Zero"
  where
    unsupported name =
      error $
        "Circuit.AD.Eliminate.runStarNet: structural "
          ++ name
          ++ " nodes are not supported; fuse them into Lifts first"

-- | Solve a single affine knot whose channel type matches the top-level
-- proxy.
solveKnot ::
  (StarChannel j, Additive (->) j) =>
  Proxy j ->
  Net StarPullback (,) (j, c) (j, b) ->
  StarPullback c b
solveKnot proxy body = traceStarPullback (runStarNet proxy body)
