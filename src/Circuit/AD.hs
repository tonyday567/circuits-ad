{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Reverse-mode automatic differentiation via a lens-shaped base arrow.
--
-- 'Diff' is a differentiable function @a -> b@ that carries its own pullback:
-- given a cotangent @db@ on the output, produce a cotangent @da@ on the input.
-- This is the same shape as Conal Elliott's \"Simple Essence of AD\" reverse
-- mode, lifted into a 'Category' so it can be used as the base arrow for
-- 'Trace'.
--
-- With the 'Trace' @(,)@ instance, 'realise' \"Trace Diff\" runs forward and
-- pulls back — reverse-mode AD with no GADT changes.  The backward pass
-- through a 'Knot' uses a lazy fixpoint (the implicit function theorem):
-- the gradient at a fixed point solves its own affine equation.
--
-- = Example
--
-- Differentiating @x²@ through a circuit:
--
-- >>> import Circuit.Trace (Trace(..), run)
-- >>> import Circuit.AD
-- >>> import Prelude hiding (Monoid, id, (.))
-- >>> let f = Arr (Diff (\x -> (x * x, \dx' -> 2 * x * dx'))) :: Trace (,) Diff Double Double
-- >>> let (y, pullback) = runDiff (run f) 3.0
-- >>> y
-- 9.0
-- >>> pullback 1.0
-- 6.0
module Circuit.AD
  ( -- * Untagged differentiable arrow
    Diff,

    -- * Tagged differentiable arrow
    Diff',

    -- * Constructor pattern
    pattern Diff,

    -- * Runner
    runDiff,

    -- * Trace variants
    traceNFrom,
    traceStarFrom,
    traceStar,

    -- * Inspectable backprop
    backprop,
    linearizeAt,
    fromDiffAt,

    -- * Linear pullback arrow
    Pullback,

    -- * Smoke tests
    quadD,
  )
where

import Circuit.AD.Pullback (Pullback (..))
import Circuit.Dagger (Comonoid (..), Monoid (..))
import Circuit.Dagger qualified as CD
import Circuit.Monoidal (Action (..), Tensor (..))
import Circuit.Monoidal.Category (Monoidal (..))
import Circuit.Net (Net (..))
import Circuit.Net qualified
import Circuit.Trace (Traced (..))
import Circuit.Trace qualified as C
import Control.Category
import Data.Bifunctor
import NumHask.Algebra.Additive qualified as NHA
import NumHask.Algebra.Multiplicative qualified as NHM
import NumHask.Algebra.Ring qualified as NHR
import NumHask.Diff (Diff, Diff', runDiff, pattern Diff)
import Prelude hiding (Monoid, id, (.))

-- $setup
-- >>> import Circuit.Trace (Trace (..), run)
-- >>> import Prelude hiding (id, (.))

-- | 'Trace' for 'Diff' with the @(,)@ tensor.
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
instance Traced (,) (Diff' p) where
  trace (Diff body) = Diff $ \b ->
    let -- Forward: standard lazy knot
        ~((a, c), backward) = body (a, b)
        -- Backward: same shape, transposed — knot through the pair
        pullback dc =
          let bd = backward (fst bd, dc)
           in snd bd
     in (c, pullback)

  untrace (Diff f) = Diff $ \(a, b) ->
    let (c, back) = f b
     in ((a, c), Data.Bifunctor.second back)

-- | Cartesian channel plumbing for 'Diff'.
instance Monoidal (,) (Diff' p) where
  assoc = Diff (\((s, s'), x) -> ((s, (s', x)), \(s'', (s''', x')) -> ((s'', s'''), x')))
  assoc' = Diff (\(s, (s', x)) -> (((s, s'), x), \((s'', s'''), x') -> (s'', (s''', x'))))
  braid = Diff (\(s, (s', x)) -> ((s', (s, x)), \(s'', (s''', x')) -> (s''', (s'', x'))))

-- | Cocartesian channel plumbing for 'Diff'.
instance Monoidal Either (Diff' p) where
  assoc =
    Diff
      ( \case
          Left (Left a) -> (Left a, \case Left da -> Left (Left da); Right _ -> error "assoc")
          Left (Right b) -> (Right (Left b), \case Right (Left db) -> Left (Right db); _ -> error "assoc")
          Right c -> (Right (Right c), \case Right (Right dc) -> Right dc; _ -> error "assoc")
      )
  assoc' =
    Diff
      ( \case
          Left a -> (Left (Left a), \case Left (Left da) -> Left da; _ -> error "assoc'")
          Right (Left b) -> (Left (Right b), \case Left (Right db) -> Right (Left db); _ -> error "assoc'")
          Right (Right c) -> (Right c, \case Right dc -> Right (Right dc); _ -> error "assoc'")
      )
  braid =
    Diff
      ( \case
          Left a -> (Right (Left a), \case Right (Left da) -> Left da; _ -> error "braid")
          Right (Left b) -> (Left b, \case Left db -> Right (Left db); _ -> error "braid")
          Right (Right c) -> (Right (Right c), \case Right (Right dc) -> Right (Right dc); _ -> error "braid")
      )

-- | Trace for 'Diff' with the 'Either' tensor.
--
-- The 'Either' trace is a while-loop: 'Left a' means "iterate again",
-- 'Right c' means "return".  Forward pass runs until the body produces a
-- 'Right', recording each body's pullback.  Backward pass replays those
-- pullbacks in reverse order, propagating the output cotangent back through
-- the iteration chain.
--
-- The number of iterations is treated as locally constant by the derivative:
-- small perturbations of the input do not change the branch sequence.  This
-- is the standard reverse-mode treatment of data-dependent control flow.
--
-- __Proof obligation__ (joins the linearity obligation on the other
-- traces): a cotangent on a sum is represented as the /same/ sum, and
-- its tag must match the primal trajectory — the cotangent space at a
-- point of @Either a c@ is the cotangent space of the branch the point
-- is in.  Every honest pullback maps an output-tagged cotangent to an
-- input-tagged one; the replay errors loudly on any mismatch rather
-- than misreading a dishonest primitive.
--
-- A loop with an exact hand-computable derivative — double three
-- times (channel carries @(countdown, acc)@), so @y = 8x@:
--
-- >>> :{
-- let step = Diff (\e -> case e of
--       Right x -> (Left (3 :: Double, x :: Double), \de -> case de of
--         Left (_, dv) -> Right dv
--         Right _ -> error "tag")
--       Left (k, v)
--         | k <= 0 -> (Right v, \de -> case de of
--             Right dc -> Left (0, dc)
--             Left _ -> error "tag")
--         | otherwise -> (Left (k - 1, 2 * v), \de -> case de of
--             Left (dk, dv) -> Left (dk, 2 * dv)
--             Right _ -> error "tag"))
-- :}
--
-- >>> let (y, pb) = runDiff (trace step) 1.5
-- >>> y
-- 12.0
-- >>> pb 1.0
-- 8.0
instance Traced Either (Diff' p) where
  trace (Diff body) = Diff $ \b ->
    let -- Forward: iterate, collecting pullbacks in execution order.
        goFwd x =
          let (y, pb) = body x
           in case y of
                Right c' -> (c', [pb])
                Left a ->
                  let (c', pbs') = goFwd (Left a)
                   in (c', pb : pbs')
        (c, pbs) = goFwd (Right b)
        -- Reverse the tape once; shared across all cotangents.
        rpbs = reverse pbs
        -- Backward: replay pullbacks in reverse order.
        pullback dc =
          case rpbs of
            [] -> error "Circuit.AD.Trace Diff Either: empty loop (impossible)"
            (lastPb : prevPbs) -> goBwd (lastPb (Right dc)) prevPbs
          where
            goBwd (Right db) [] = db
            goBwd (Left _) [] =
              error "Circuit.AD.Trace Diff Either: final cotangent landed on Left (impossible)"
            goBwd (Left da) (pb : pbs') = goBwd (pb (Left da)) pbs'
            goBwd (Right _) (_ : _) =
              -- A Right-tagged cotangent with pullbacks still pending means
              -- some pullback at iteration i > 1 claimed its input was the
              -- exit branch — but that iteration's primal input was 'Left'.
              -- Returning here would silently skip the remaining chain rule,
              -- so this is a dishonest primitive, not an early exit.
              error "Circuit.AD.Trace Diff Either: Right cotangent mid-chain (tag-dishonest pullback)"
     in (c, pullback)

  untrace (Diff f) = Diff $ \case
    Left a -> (Left a, \case Left da -> Left da; Right _ -> error "untrace: Left input, Right cotangent")
    Right b ->
      let (c, back) = f b
       in (Right c, \case Right dc -> Right (back dc); Left _ -> error "untrace: Right input, Left cotangent")

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
  (Monoid (->) a) =>
  a ->
  Int ->
  Diff' p (a, b) (a, c) ->
  Diff' p b c
traceNFrom x0 n (Diff body) = Diff $ \b ->
  let -- Forward: iterate from caller-supplied seed
      stepFwd x = let ((x', _), _) = body (x, b) in x'
      a = iterate stepFwd x0 !! n
      ((_, c), backward) = body (a, b)
      -- Backward: iterate from zero, extract result once
      pullback dc =
        let stepBwd d = fst (backward (d, dc))
            da = iterate stepBwd (CD.zero ()) !! n
         in snd (backward (da, dc))
   in (c, pullback)

-- ---------------------------------------------------------------------------
-- StarSemiring — the principled Neumann index
-- ---------------------------------------------------------------------------

-- | Trace with a closed-form backward pass via the Kleene 'NHR.star'.
--
-- The integer @n@ in 'traceNFrom' truncates a series on /both/ passes.
-- But only the forward fixpoint is genuinely nonlinear; the backward
-- channel equation is affine — calculus promises linearity in
-- cotangents:
--
-- > da = A·da + C·dc        solution:  da = star A · C·dc
--
-- with @star a = one + a·star a@ — the Neumann series as algebra,
-- @1\/(1−a)@ over a field.  Because the pullback is linear, the
-- blocks A and C·dc are /extractable by probing/:
--
-- > backward (dj, dc) = (A·dj + C·dc, B·dj + D·dc)
-- > A    = fst (backward (one,  0))   -- channel self-coupling
-- > C·dc = fst (backward (zero, dc))
--
-- and the trace's pullback is the Schur complement
-- @D·dc + B·star A·C·dc@, recovered with one more probe at the
-- backward fixpoint:
--
-- > db = snd (backward (star A · C·dc, dc))
--
-- (Check: @A·(star A·C·dc) + C·dc = (A·star A + one)·C·dc
-- = star A·C·dc@ — the star law discharges the fixpoint.)
--
-- So: forward still iterates from the caller's seed (no closed form
-- exists for an arbitrary nonlinear fixpoint), but the backward pass
-- is /exact/ in three calls to @backward@ — no Neumann index at all.
-- The @star@ probe is computed once per forward point and shared
-- across all cotangents.
--
-- The closed form is the truncated iteration's limit; pure-Prelude
-- witness at @a = 0.3@, @c = 2@:
--
-- >>> let daIter = iterate (\d -> 0.3 * d + 2.0 * 1.0) 0 !! 200
-- >>> abs (daIter - 1.0 / (1.0 - 0.3) * 2.0) < 1e-12
-- True
--
-- __Caveat__: @numhask@ declares 'NHR.StarSemiring' but ships no
-- instances; the only carriers in the tower are
-- 'NumHask.Free.Carriers.FieldStar' (@star a = recip (1−a)@),
-- @Warshall@, and @MinPlus@.  For bare 'Double' channels and for /vector/
-- channels solved by 'Circuit.AD.Matrix.starMatrix', see
-- @Circuit.AD.Star@ — the Schur-complement bridge proper.
--
-- __Proof obligation__: the probes assume the pullback is linear.
-- Every honestly-constructed 'Diff' primitive satisfies this (a
-- pullback /is/ a linear map); a primitive whose backward closure is
-- affine-with-offset is a bug that this function will silently
-- misread.
traceStarFrom ::
  (NHR.StarSemiring j, Monoid (->) c) =>
  -- | forward seed
  j ->
  -- | forward iteration count
  Int ->
  Diff' p (j, b) (j, c) ->
  Diff' p b c
traceStarFrom x0 n (Diff body) = Diff $ \b ->
  let -- Forward: iterate from caller-supplied seed (as 'traceNFrom')
      stepFwd x = let ((x', _), _) = body (x, b) in x'
      a = iterate stepFwd x0 !! n
      ((_, c), backward) = body (a, b)
      -- Probe the channel self-coupling once; star it in closed form
      aStar = NHR.star (fst (backward (NHM.one, CD.zero ())))
      -- Backward: exact in two more probes — no iteration
      pullback dc =
        let cdc = fst (backward (NHA.zero, dc))
         in snd (backward (aStar NHM.* cdc, dc))
   in (c, pullback)

-- | Trace via the Kleene star — the execution formula, lazy form.
--
-- For a knot body with channel self-coupling block A and cross-blocks
-- B, C, D, the trace is the Schur complement:
--
-- > traceStar f = D + B · star A · C
--
-- The lazy 'trace' instance for 'Diff' computes exactly this via a
-- lazy fixpoint rather than closed form, so this alias is definable
-- without using 'NHR.star' at all — the constraint records the
-- /semantics/, not the implementation.  Note that @numhask@ ships no
-- 'NHR.StarSemiring' instances, so for concrete carriers prefer
-- 'traceStarFrom' (scalar channel, closed-form backward) or
-- @Circuit.AD.Star.traceStarMatrix@ (vector channel, solved by
-- 'Circuit.AD.Matrix.starMatrix' — the bridge made literal).
traceStar :: (NHR.StarSemiring j) => Diff' p (j, b) (j, c) -> Diff' p b c
traceStar = trace

-- | Pointwise linearization: run a 'Net Diff' forward at @a@ and
-- build the transposed net of pullbacks.
--
-- This is the same operation as /backpropagation/, but read forwards
-- through the lens of 'linearize': the graph's structure is burned down
-- into a straight linear (affine) cotangent map.  'backprop' is the dual
-- view — looking backwards, the single output cotangent appears to
-- bifurcate and fan out through the wiring.  Propagate fans values out in
-- the forward direction; linearize straightens them into a wire in the
-- reverse direction.
--
-- This is the honest reverse-mode gradient net.  'transpose' alone is
-- only correct for linear nets; for nonlinear 'Diff' primitives the
-- pullback closure depends on the primal point.  'linearizeAt' runs
-- the net, captures each primitive's pullback at the point it saw,
-- and returns both the output value and a 'Net Pullback' whose wires
-- are those pointwise pullbacks composed in reverse order.
--
-- Use 'Circuit.AD.Pullback.evalPullback' to evaluate the resulting net
-- at a single output cotangent.
--
-- __Caveat__: /Fixpoints are lazy on both passes./  Forward 'Trace's tie
-- the same lazy knot as 'Trace' @Diff@; the 'Trace's in the returned net
-- tie the lazy 'Trace' @Pullback@ knot.  For strict carriers with
-- nonzero channel self-coupling, /both/ diverge.  The forward side needs
-- an iteration policy (a @backpropNFrom@, mirroring 'traceNFrom').  The
-- backward side deserves better: the pullback net is linear by
-- construction, so its knots satisfy affine equations and can be
-- /eliminated/ — probe the knot body for its channel matrix,
-- 'Circuit.AD.Matrix.starMatrix' it, and replace the 'Trace' with a 'Lift'.
-- That elimination pass is state elimination on a linear circuit: the
-- linear-representation normal form that @kleeneSimplify@ gestures at,
-- landing where it can actually be lawful.
--
-- >>> import Circuit.Net (Net (..))
-- >>> import Circuit.AD.Pullback (evalPullback)
-- >>> let sq = Diff (\x -> (x * x, \d -> 2 * x * d))
-- >>> let n = Compose (Lift (CD.plus :: Diff (Double, Double) Double)) (Compose (Par (Lift sq) (Lift sq)) Copy) :: Net (,) Diff Double Double
-- >>> let (y, g) = backprop n 3.0
-- >>> y
-- 18.0
-- >>> evalPullback g 1.0
-- 12.0
backprop ::
  forall p a b.
  Net (,) (Diff' p) a b ->
  a ->
  (b, Net (,) Pullback b a)
backprop = linearizeAt

-- | Capture the pullback of a 'Diff' primitive at a primal point.
--
-- >>> let d = Diff (\x -> (x * x, \dy -> 2 * x * dy))
-- >>> runPullback (fromDiffAt d 3) 1
-- 6
fromDiffAt :: forall p a b. Diff' p a b -> a -> Pullback b a
fromDiffAt (Diff f) a = Pullback (snd (f a))
{-# INLINE fromDiffAt #-}

-- | Run a 'Net Diff' forward and build the transposed pullback net.
--
-- This linearizes the 'Net' directly, without 'Circuit.Net.melt', so
-- 'Trace's inside 'Par' arms survive as 'Trace's in the pullback net.
linearizeAt ::
  forall p a b.
  Net (,) (Diff' p) a b ->
  a ->
  (b, Net (,) Pullback b a)
linearizeAt = linearizeNet

-- | Pointwise linearization over the free 'Net' language.
--
-- 'Par' is preserved as 'Par'.  Structural rows ('Copy', 'Add',
-- 'Discard', 'Zero') are converted to point-independent 'Lift'
-- pullbacks using the 'Diff' dictionaries the constructors already
-- carry (copy↦plus, add↦dup, discard↦zero, zero↦discard).  Because the
-- recursion never melts the net into a 'Trace' first, feedback loops
-- under 'Par' remain visible to future star-elimination passes.
linearizeNet ::
  forall p a b.
  Net (,) (Diff' p) a b ->
  a ->
  (b, Net (,) Pullback b a)
linearizeNet n a = case n of
  Lift d ->
    let (b, pb) = runDiff d a
     in (b, Lift (Pullback pb))
  Compose g f ->
    let (b, f') = linearizeNet f a
        (c, g') = linearizeNet g b
     in (c, Compose f' g')
  Par f g ->
    let (a1, a2) = a
        (b, f') = linearizeNet f a1
        (d, g') = linearizeNet g a2
     in ((b, d), Par f' g')
  Swap ->
    let (x, y) = a
     in ((y, x), Swap)
  Copy ->
    ((a, a), Lift (Pullback (\(db1, db2) -> fst (runDiff (plus @(Diff' p) @a) (db1, db2)))))
  Discard ->
    ((), Lift (Pullback (\_ -> fst (runDiff (zero @(Diff' p) @a) ()))))
  Plus ->
    let (x, y) = a
     in (fst (runDiff (plus @(Diff' p) @b) (x, y)), Lift (Pullback (\dc -> (dc, dc))))
  Zero ->
    (fst (runDiff (zero @(Diff' p) @b) ()), Lift (Pullback (const ())))
  Knot f ->
    let ~((x, b), f') = linearizeNet f (x, a)
     in (b, Knot f')

-- | Pointwise linearization over the core 'Trace' language.  The
-- bimonoid rows ('Copy', 'Plus', ...) have already been melted into
-- 'Arr's by 'Circuit.Net.melt', so this recursion only sees 'Arr' and
-- 'Knot'.
linearizeCircuit ::
  forall p a b.
  C.Trace (,) (Diff' p) a b ->
  a ->
  (b, Net (,) Pullback b a)
linearizeCircuit (C.Arr (Diff f)) a =
  let (b, pb) = f a
   in (b, Lift (Pullback pb))
linearizeCircuit (C.Knot f) a =
  let ~((x, b), pb) = runDiff f (x, a)
   in (b, Knot (Lift (Pullback pb)))

-- ---------------------------------------------------------------------------
-- Comonoid Diff — copy and discard for the differentiable arrow.
--
-- In Diff, the bimonoid is self-dual under differentiation: copy's pullback
-- is plus, discard's pullback is zero, plus's pullback is dup, zero's
-- pullback is discard.  transpose's Copy ↔ Add, Discard ↔ Zero table is
-- not a rule imposed on syntax — it's the instance structure of Diff read
-- off at the semantic level.

-- | Copy in D: the pullback is 'plus' (fan-in on the backward pass).
--
-- >>> import Circuit.Monoidal (Action(..))
-- >>> import Circuit.Dagger (Comonoid(..))
-- >>> let (_, pb) = runDiff (dup :: Diff Int (Int, Int)) 5
-- >>> pb (1, 2)
-- 3
instance (Monoid (->) a) => Comonoid (Diff' p) a where
  copy = Diff (\a -> ((a, a), CD.plus))
  {-# INLINE copy #-}

  discard = Diff (const ((), \() -> CD.zero ()))
  {-# INLINE discard #-}

-- | Add in D: the pullback is 'copy' (fan-out on the backward pass).
--
-- >>> let (_, pb) = runDiff (plus :: Diff (Int, Int) Int) (3, 4)
-- >>> pb 1
-- (1,1)
instance (Monoid (->) a) => Monoid (Diff' p) a where
  plus = Diff (\(a, b) -> (CD.plus (a, b), \d -> (d, d)))
  {-# INLINE plus #-}

  zero = Diff (\() -> (CD.zero (), const ()))
  {-# INLINE zero #-}

-- | Monoidal product for Diff: independent wires, no additive constraint.
--
-- >>> let f = Diff (\x -> (x + 1, \d -> d)) :: Diff Int Int
-- >>> let g = Diff (\x -> (x * 2, \d -> 2 * d)) :: Diff Int Int
-- >>> let (y, pb) = runDiff (par f g) (3, 4)
-- >>> y
-- (4,8)
-- >>> pb (1, 1)
-- (1,2)
instance Tensor (,) (Diff' p) where
  par (Diff f) (Diff g) = Diff $ \(a, c) ->
    let (b, fb) = f a; (d, gd) = g c
     in ((b, d), Data.Bifunctor.bimap fb gd)
  {-# INLINE par #-}

instance Action (,) (Diff' p) where
  swap = Diff (\(a, b) -> ((b, a), \(db, da) -> (da, db)))
  {-# INLINE swap #-}

-- ---------------------------------------------------------------------------
-- Smoke test: quadratic — the term that was impossible in Stage 1
-- ---------------------------------------------------------------------------

-- | @2x² + 3x + 5@ built from 'par', 'dup', and 'plus' on the @Diff@ arrow.
-- No 'Net' needed — the instances are the denotations the rows will realise to.
--
-- The gradient is @4x + 3@, so at @x = 1@: value 10, gradient 7.
--
-- >>> let (y, pb) = runDiff quadD 1.0
-- >>> y
-- 10.0
-- >>> pb 1.0
-- 7.0
quadD :: Diff' p Double Double
quadD = CD.plus . par sq lin . CD.copy
  where
    sq = Diff (\x -> (2 * x * x, \d -> 4 * x * d))
    lin = Diff (\x -> (3 * x + 5, (3 *)))
