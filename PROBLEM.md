# Erdős Problem #410

## Problem Statement

Let $\sigma_1(n) = \sigma(n)$, the sum of divisors function, and $\sigma_k(n) = \sigma(\sigma_{k-1}(n))$.

Is it true that for all $n \geq 2$,

$$\lim_{k \to \infty} \sigma_k(n)^{1/k} = \infty?$$

The theorem states that iterated application of the sum-of-divisors function grows super-exponentially — i.e., faster than any geometric sequence $c^k$ — for every starting value $n \geq 2$.

## Lean4 Formal Theorem

```lean
open ArithmeticFunction Filter

theorem erdos_410 : ∀ n > 1,
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  sorry
```

## Goal
The goal is to produce a natural language proof as well as a Lean proof of the theorem.

Success criteria:

1. The main theorem *statement* in Lean corresponds to the natural language problem statement and does not make additional assumptions. If a statement was provided, it should not be changed. Do not try to make the problem easier.
2. The Lean theorem compiles with `lake build`
3. There are no sorrys in the codebase. Upstream sorrys stemming from inside of mathlib are acceptable, but you may *not* introduce new ones.

ALL THREE MUST BE SATISFIED FOR SUCCESS
