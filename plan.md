# Plan: star-elimination of `(,)`-knots and phantom-tagged `Diff`

## Goals
1. Implement a star-elimination pass on linear `Net (,) Pullback` nets.
2. Add a phantom type parameter to `Diff` so nested AD cannot mix perturbation tags.
3. Add robust tests and clearly separate `circuits` (generic wiring) from `circuits-ad` (AD-specific algorithms).

## 1. Star-elimination pass on `Net Pullback`

### Where it lives
- `circuits` owns `Net`, the structural language.
- `circuits-ad` owns `Pullback`, `Diff`, `Matrix`/`StarSemiring` usage, and the elimination pass.
- The new module will be `Circuit.AD.Eliminate` in `circuits-ad`.

### Design (recommended)
Introduce a small AD-specific class `StarChannel j` that abstracts over scalar and vector feedback channels:

```haskell
class (NHR.StarSemiring (Scalar j), NHA.Additive (Scalar j), NHM.Multiplicative (Scalar j)) => StarChannel j where
  type Scalar j
  channelDim  :: j -> Int
  zeroChannel :: Int -> j
  basisChannel :: Int -> Int -> j
  selfMatrix  :: (j -> j) -> Matrix (Scalar j)
  applyStar   :: Matrix (Scalar j) -> j -> j
```

Instances:
- `StarChannel FieldStar` (1-D channel).
- `StarChannel [a]` for any `NHR.StarSemiring a` with the needed `Additive`/`Multiplicative` structure (n-D channel).

API:

```haskell
starEliminateKnot ::
  (StarChannel j, Additive (->) c) =>
  Net (,) Pullback (j, b) (j, c) ->
  Net (,) Pullback b c

eliminateKnotsUniform ::
  (StarChannel j, Additive (->) c) =>
  Proxy j ->
  Net (,) Pullback b c ->
  Net (,) Pullback b c
```

`starEliminateKnot` first recursively eliminates inner knots (uniform-channel assumption), probes the linear body for the self-coupling matrix `A`, the cross block `C·dc`, applies `starMatrix`/`NHR.star`, and replaces the `Knot` with a single `Lift (Pullback (\dc -> ...))`.

`eliminateKnotsUniform` walks the net and applies `starEliminateKnot` at every `Knot`. It requires a `Proxy j` witness because the channel type is existential in `Net`.

### Why this design
- It reuses the existing `Hasknum.Matrix.starMatrix` and `NHR.StarSemiring` infrastructure.
- It handles both scalar `Double` channels (via `FieldStar`) and vector `[Double]` channels (via `[FieldStar]`).
- It is a compile-time net transformation, not a runtime interpretation, so the resulting net can be evaluated without the lazy-knot divergence.
- It keeps generic `Net` machinery in `circuits`; only AD-specific matrix probing lives in `circuits-ad`.

### Alternative considered
A generic `foldNet` in `circuits` would make many passes (including this one) more uniform, but it is a larger refactor and would touch `transpose`, `fuse`, `runNet`, and `forget`. We defer it.

## 2. Phantom type parameter for `Diff`

### Design (recommended)
Make `Diff` phantom-tagged but keep the existing name usable:

```haskell
newtype Diff' (p :: k) a b = Diff'
  { runDiff' :: a -> (b, b -> a)
  }

type Diff = Diff' ()

pattern Diff :: (a -> (b, b -> a)) -> Diff' p a b
pattern Diff f = Diff' f

runDiff :: Diff' p a b -> a -> (b, b -> a)
runDiff = runDiff'
```

All instances become polymorphic in the tag:

```haskell
instance Category (Diff' p)
instance Trace (Diff' p) (,)
instance Trace (Diff' p) Either
instance MonoidalP (Diff' p)
...
```

### Why this design
- Existing code `Diff a b`, `Net Diff`, `Circuit Diff` continues to work because `Diff` is a synonym for `Diff' ()`.
- New tagged code uses `Diff' Tag a b` or `Net (Diff' Tag)`.
- Composition across different tags is rejected by the `Category` instance.
- No changes are needed in the `circuits` package.

### Alternative considered
Rename `Diff` to `Diff' ()` everywhere. That is cleaner long-term but breaks every existing type signature and doctest. The backward-compatible synonym avoids that breakage while still giving us the phantom machinery.

## 3. Tests

### Star-elimination tests (new `test/StarEliminate.hs`)
- Direct scalar pullback knot with non-zero channel self-coupling; evaluate the eliminated net and compare with the analytic closed form.
- Direct vector pullback knot (channel length 2) with a non-trivial self-coupling matrix; compare with the analytic closed form.
- Integration test: linearize a `Net Diff` lazy knot (zero forward self-coupling), then run `eliminateKnotsUniform`; the gradient must agree with the un-eliminated net.

### Phantom-tag tests (new `test/Tags.hs`)
- Positive: `Diff' Tag1` values compose with `Diff' Tag1` and produce the same numeric results as untagged `Diff`.
- Positive: a nested-AD scenario where an outer `Diff' Outer` operates over values of type `Diff' Inner Double Double` using the `Num`/`NumHask` instances compiles and runs.
- Compile-time separation is demonstrated by type signatures; the `Category` instance prevents mixing tags.

### Existing smoke tests
- Update `test/Verify.hs` type ascriptions only if the synonym expansion requires it (expected minimal changes).
- Keep all existing assertions passing.

## 4. Files to change

- `src/Circuit/AD.hs` — redefine `Diff` with phantom tag, update instances and exports.
- `src/Circuit/AD/NumHask.hs` — update instance heads to `Diff' p s b`.
- `src/Circuit/AD/Pullback.hs` — no structural change; confirm `Pullback` remains untagged.
- `src/Circuit/AD/Star.hs` — update signatures to `Diff' p`.
- `src/Circuit/AD/Oracle.hs` — update signatures to `Diff' p`.
- `src/Circuit/AD/Eliminate.hs` — new module.
- `test/Verify.hs` — import and run new test modules.
- `test/StarEliminate.hs` — new.
- `test/Tags.hs` — new.
- `circuits-ad.cabal` — add `Circuit.AD.Eliminate` to `exposed-modules` and new test modules to `other-modules`.

## 5. Verification
- `cabal build all`
- `cabal test`
- `cabal-docspec`

## 6. Notes on `circuits` vs `circuits-ad`
- `circuits` keeps `Net`, `Circuit`, `Trace`, `Additive`, `Dup`, `MonoidalP` unchanged.
- `circuits-ad` owns the AD arrow (`Diff`), the pullback arrow (`Pullback`), the star/matrix bridge (`Star`), and the new elimination pass (`Eliminate`).
- If we later want a generic `Net` fold or traversal, that belongs in `circuits`; it is not required for this task.
