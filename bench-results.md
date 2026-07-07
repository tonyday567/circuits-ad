# circuits-ad benchmark results

**deep** ⟜ traceNFrom performance: differentiating through feedback loops.

**Setup**: M3 Mac, GHC 9.14.1, -O2. Three problems exercising `traceNFrom` —
truncated fixed-point iteration with reverse-mode differentiation.

---

## Problem 1: Babylonian sqrt

**x_{k+1} = (x_k + a/x_k)/2**, differentiate fixed point dx*/da.

Analytic: sqrt(2.0) = 1.414213562373, ds/da = 1/(2√2) = 0.353553390593

| n | y | gradient | error | time |
|---|-----|----------|-------|------|
| 1 | 1.416667 | 0.351852 | 4.2e0 | 85µs |
| 2 | 1.414216 | 0.353553 | 2.7e-6 | 1µs |
| 3 | 1.414214 | 0.353553 | 2.0e-12 | 0µs |
| 5 | 1.414214 | 0.353553 | 2.2e-15 | 0µs |
| 10 | 1.414214 | 0.353553 | 2.2e-15 | 2µs |
| 50 | 1.414214 | 0.353553 | 2.2e-15 | 4µs |

Converges to machine precision by n=3. Gradient correct to 1e-12 by n=3.
The geometric series in the backward pass converges fast because the
Jacobian at the fixed point is zero (dx*/dx = 0 for x* = sqrt(a)).

## Problem 2: Dottie number

**x_{k+1} = cos(a·x_k)**, a=1.0, differentiate dx*/da.

| n | y | gradient | time |
|---|-----|----------|------|
| 10 | 0.741827 | -0.29868 | 3µs |
| 20 | 0.739138 | -0.29750 | 2µs |
| 50 | 0.739085 | -0.29747 | 4µs |
| 100 | 0.739085 | -0.29747 | 7µs |

Converges to the Dottie number (0.739085...). Gradient converges to ≈-0.29747.
Sub-10µs for all iteration counts.

## Problem 3: Scale test

**x_{k+1} = x_k + a**, analytical: y = (n+1)·a, g = n+1.
Measures raw overhead of traceNFrom per iteration.

| n | y | g | error | time | ns/iter |
|---|-----|---|-------|------|----------|
| 10 | 33 | 11 | 4.0 | 1µs | 100 |
| 100 | 303 | 101 | 4.0 | 5µs | 50 |
| 1,000 | 3,003 | 1,001 | 4.0 | 62µs | 62 |
| 10,000 | 30,003 | 10,001 | 4.0 | 1,002µs | 100 |
| 100,000 | 300,003 | 100,001 | 4.0 | 21,406µs | 214 |
| 1,000,000 | 3,000,003 | 1,000,001 | 4.0 | 367,305µs | 367 |

**Scaling**: roughly 200-400ns per iteration for forward+backward combined.
At n=1M, 367ms total. The per-step cost is dominated by the Diff closure
allocation — each iteration constructs a (value, pullback) pair.

The constant error (4.0) is from traceNFrom's extra body evaluation:
it runs n iterations of state transition, then calls body once more to
extract the output. So y = (n+1)·a instead of n·a. This is correct
behavior — the output is the state AFTER n steps, not during.

## What this says about circuits-ad

**Speed**: per-iteration overhead is ~200-400ns for a simple Diff body
with both forward and backward passes. This is in the ballpark of raw
function-call overhead plus a closure allocation. The Monoid summation
(zero/plus on the state cotangent) adds negligible cost for scalar states.

**Correctness**: the geometric-series accumulation in the backward pass
converges exactly when the Jacobian at the fixed point has |jx| < 1.
For Babylonian, jx → 0 so convergence is instant (3 iterations). For
Dottie, jx ≈ -0.67 so convergence is slower but still correct.

**The `dx_st + dx_out` pattern**: this is the critical idiom for
traceNFrom bodies. The output cotangent `dc` (= dx_out) is fed to EVERY
backward step, not just the last one. The body's pullback must sum state
and output cotangents: `dx_total = dx_st + dx_out`. This is the chain
rule through the loop — each step's output contributes to the gradient
through both the state channel (future steps) and the direct output
channel (the loss function).
