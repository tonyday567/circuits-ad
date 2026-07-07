# How linearizeNet dissolved

**deep** ⟜ a close reading of the SigLens × circuits-ad unification.
What we had, what we have now, and what fell away.

---

## Before

**circuits-ad 0.1** ⟜ two-phase reverse-mode AD. Build a `Net Diff`, run it
forward, capture pullbacks, build a backward `Net Pullback`, run that. The
bridge between phases was `linearizeNet` — a 40-line recursive function that
pattern-matched every Net constructor.

```haskell
linearizeNet :: Net (,) (Diff' p) a b -> a -> (b, Net (,) Pullback b a)
linearizeNet n a = case n of
  Lift d    -> let (b, pb) = runDiff d a in (b, Lift (Pullback pb))
  Compose g f -> let (b, f') = linearizeNet f a
                     (c, g') = linearizeNet g b
                  in (c, Compose f' g')
  Par f g   -> let (a1, a2) = a; (b, f') = linearizeNet f a1; (d, g') = linearizeNet g a2
                in ((b, d), Par f' g')
  Swap      -> let (x, y) = a in ((y, x), Swap)
  Copy      -> ((a, a), Lift (Pullback (\(db1, db2) -> fst (runDiff (plus @(Diff' p) @a) (db1, db2)))))
  Discard   -> ((), Lift (Pullback (\_ -> fst (runDiff (zero @(Diff' p) @a) ()))))
  Plus      -> let (x, y) = a in (fst (runDiff (plus @(Diff' p) @b) (x, y)), Lift (Pullback (\dc -> (dc, dc))))
  Zero      -> (fst (runDiff (zero @(Diff' p) @b) ()), Lift (Pullback (const ())))
  Trace f   -> let ~((x, b), f') = linearizeNet f (x, a) in (b, Trace f')
```

**The problem** ⟜ this function knows too much. It knows how to compose
pullbacks in reverse order. It knows that Copy's backward is Plus. It knows
that Trace needs a lazy knot on the forward pass. It is the *transpose* of a
differentiable net, hand-rolled as structural recursion over a GADT. If you
add a new constructor to Net, you must teach `linearizeNet` about it. If you
want to inspect the backward net before evaluating it, you must write
another pass over `Net Pullback`.

## After

**SigLensCat × Diff** ⟜ one-phase forward/backward. Build a `SigLensTrace`
over `SomeLens (->)`, call `fold`, get both directions in one arrow.

```haskell
diffAsLens :: Diff a b -> SomeLens (->) a b
diffAsLens (Diff f) = SomeLens (Lens get put)
  where
    get a = let (b, pb) = f a in (pb, b)
    put (pb, b') = pb b'

runLens :: SomeLens (->) a b -> a -> (b, b -> a)
runLens (SomeLens (Lens get put)) a =
  let (r, b) = get a
   in (b, \db -> put (r, db))
```

**SigLensCat** ⟜ free category of lens diagrams:

```haskell
type SigLensCat arr = Free SigCompose (SomeLens arr)
```

**SigLensTrace** ⟜ free traced category of lenses:

```haskell
type SigLensTrace arr = SigTrace (,) (SomeLens arr)
```

**Interpretation** ⟜ one call:

```haskell
fold :: SigLensTrace (->) a b -> SomeLens (->) a b
```

Then `runLens` extracts both the forward result and the backward pullback.

## What dissolved

**The `Lift` case.** `linearizeNet` evaluated Diff at a point, captured the
pullback, wrapped it in `Pullback`. In the new design, `diffAsLens` stores
the pullback as the *residual* of the lens. The getter evaluates Diff at the
input point; the residual `r` captures the point-specific pullback. The
putter applies the pullback. This is the same operation, but the residual
lives inside the arrow, not as a separate GADT.

**The `Compose` case.** `linearizeNet` recursed into both sides and composed
the resulting pullback nets *in reverse order*: `Compose f' g'` when the
source had `Compose g f`. This reversal is the chain rule — the backward
pass composes in opposite order to the forward pass.

In the new design, the `Category` instance for `SomeLens` handles this
automatically:

```haskell
SomeLens (Lens get2 put2) . SomeLens (Lens get1 put1) = SomeLens (Lens get put)
  where
    get = assoc' . second get2 . get1
    put = put1 . second put2 . assoc
```

The `get` chains forward: `get1` then `get2`. The `put` chains backward:
`put1` (the outer) then `put2` (the inner). The reversal is structural in
the Category instance — `put1 . second put2` where `get` was `second get2 .
get1`. No manual reversal needed. The residual merging via product
associativity (`assoc`/`assoc'`) is handled once in the instance, not
repeated in every recursive function.

**The `Trace` case.** `linearizeNet` recurred with a lazy knot on the
forward pass: `~((x, b), f') = linearizeNet f (x, a)`. The backward net
preserved the Trace constructor: `(b, Trace f')`.

In the new design, the `Strong` and `Costrong` instances on `SomeLens`
handle this. `Strong` threads an ambient wire through a lens using `braidP`
to slide the wire past the residual. `Costrong` closes the feedback loop
with the base arrow's `costrength`. These are the same operations that make
`Trace` work for ordinary arrows. No special Trace logic for lenses — the
instances compose.

**The structural rows.** `linearizeNet` had explicit patterns for `Copy`,
`Discard`, `Plus`, `Zero` — each one encoding the bimonoid self-duality by
hand (Copy's backward is Plus, etc.).

In the new design, `Diff` already has `Comonoid` and `Monoid` instances
where `copy`'s pullback IS `plus` and `discard`'s pullback IS `zero`. These
are the arrow-level instances, not structural GADT rows. The bimonoid
structure lives in the base arrow (Diff), not in the syntax. When you embed
a Diff as a SomeLens, the bimonoid structure comes along for free.

**The `Par` case.** `linearizeNet` split the input pair, recursed into both
sides, and paired the results. This is just the product bifunctor on
pullbacks — `par (Pullback f) (Pullback g) = Pullback (bimap f g)`. In the
lens setting, parallel composition isn't a separate constructor — it's
handled by the `Strong` instance that threads wires independently.

## The shift

**The intelligence moves from the recursion to the instances.** The
`Category` instance handles composition ordering (forward then backward
reversal). The `Strong`/`Costrong` instances handle trace (ambient wire
threading). The bimonoid instances on Diff handle structural self-duality
(copy ↔ plus). The `fold` function just walks the signature tree and
dispatches to these instances.

This is the exact same machinery that makes `Net` work for ordinary arrows.
`Net.transpose` is `Compose` reversal + `Copy`↔`Plus` swap at the
constructor level. `SigLensTrace.fold` is the same operation, but the
forward/backward pairing is in the arrow (Diff = SomeLens), not in a
separate syntactic transpose pass. There is no separate backward syntax to
build — the lens already carries both directions.

**linearizeNet was the transpose of a differentiable net, hand-written.**
**SigLensTrace.fold is the transpose of a lens diagram, derived from the
instances.** The 40-line recursive function became a 2-line runner:

```haskell
fold :: SigLensTrace (->) a b -> SomeLens (->) a b
-- dispatches to Category, Strong, Costrong, Bimonoid instances on SomeLens
runLens (fold diagram) a = (b, pb)  -- forward value + backward pullback, together
```

## What remains distinct

**Point-dependence.** `diffAsLens` stores the pullback function `b -> a` as
the residual. When you call `get a`, it evaluates Diff at point `a` and the
residual captures the pullback specialized to that point. If you call `get`
at a different point, you get a different pullback. This is the same as
`linearizeAt` — the backward pass only makes sense at a specific primal
point. The lens composition doesn't change this; it just threads the
point-specialized residuals through the associativity machinery.

**The Pullback type.** `Pullback` is still useful for the *linearized*
backward net — when you want to inspect the backward pass structure
independently, or eliminate knots with Kleene star. `linearizeNet` produced
a `Net Pullback` as a separate artifact. In the new design, the `Net
Pullback` is replaced by the residual structure inside the composed
SomeLens. But if you need the inspectable backward net (for star elimination
or static analysis), you still want `linearizeNet`. The new design doesn't
replace that use case — it provides a different one: running forward and
backward simultaneously without building an intermediate net.

## The equip pattern

**This is equipment.** You equip a base arrow (Diff) with lens structure
(SomeLens). The free constructions (SigLensCat, SigLensTrace) give you the
initial category with that equipment. The instances (Category, Strong,
Costrong, Bimonoid) give you the interpretation. `fold` is the unique
structure-preserving map to the base category. The adjunction tower
(SigLensTrace ⊣ SigLensCat ⊣ SomeLens ⊣ Id) makes the forgetful hierarchy
explicit.

**The same pattern works for any lens-shaped arrow.** Not just Diff.
Anything with a forward value and a backward pullback that share a residual.
The `SomeLens` wrapper is the equipment; the free constructions are the
library; the instances are the interpretation.

## Postscript: residuals for feedback channels

The lens residual is the pointwise pullback.  A separate residual appears in
feedback: every `Trace` constructor binds an existential feedback channel.
`Circuit.AD.Eliminate` solves the affine feedback equation for those channels,
but it originally had to `unsafeCoerce` the channel type because `Net.Trace`
erases it.  That was the two-knot problem: two traces may bind two different
channels, and a single global witness cannot safely represent both.

The fix is to make the channel residual explicit on the trace constructor.
`circuits` now has `TraceE` (and `SigKnotE` for the signature-based optic
category).  These constructors carry a `ChannelDict` for their channel type.
`circuits-ad` defines `StarChannelDict`, a GADT that packages a `StarChannel`
witness.  A `Diff` trace built with `traceStarNet` keeps its evidence through
`linearizeAt`; `eliminateKnots` then eliminates each knot with its own,
correct residual.  No unsafe coercion, no uniform-channel assumption.

In dependent-optics terms, `Trace` is a coend `∫^j` over the feedback channel.
`TraceE` is the same syntax plus a witness that records which residual is being
coended over.  Star elimination is the interpretation of that coend when the
body is affine in `j`.
