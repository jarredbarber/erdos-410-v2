# Density Analysis of Low-Ratio Terms

**Status:** Draft ✏️
**Author:** Pi (Agent)
**Date:** 2026-02-08

## Overview

To prove $a_k^{1/k} \to \infty$, we need the Cesàro mean of $\log(\sigma(a_k)/a_k)$ to diverge.
This requires analyzing the frequency of "low-ratio" terms and the density of "thin" numbers (where $R_k \approx 1$).

## 1. Frequency of Low-Ratio Terms ($R_k < 1.5$)

**Definition:** A term is "low-ratio" if $R_k = \sigma(a_k)/a_k < 1.5$.
Since even numbers $m$ satisfy $\sigma(m)/m \ge 1.5$ (Lemma 1.1 in `eventual-even-stability.md`), low-ratio terms correspond strictly to **odd terms**.

**Empirical Evidence:**
Simulation of the sequence for various starting values ($n \in \{2, \dots, 127\}$) shows:
- The density of low-ratio terms (odd terms) is very small ($< 10\%$).
- In many cases ($n=5, 6, 12, \dots$), the density becomes exactly 0 after a finite number of steps (Eventual Even Stability).
- `trend.py` shows that for $n=2$, odd terms disappear after step 6.

**Theoretical Bound:**
Based on `proofs/eventual-even-stability.md`:
- Conditional on Conjecture A (E-S Escape) and Conjecture B (Odd-Square Termination), the number of odd terms is **finite**.
- This implies the asymptotic density of low-ratio terms is **0**.

## 2. Density of "Thin" Even Terms

Even if $a_k$ is even ($R_k \ge 1.5$), it might be "thin" (e.g., $R_k \approx 1.5$).
For divergence, we need $R_k$ to be large often.
$R_k$ is large if $a_k$ is divisible by many small primes.

**Empirical Evidence:**
- Simulation shows `Avg_ln_R` increases from ~0.4 to >1.0 over 30 steps.
- The set of prime factors accumulates: $a_k$ eventually becomes divisible by 3, 5, 7, etc.
- For $n=2$, at $k=30$, $a_k$ is divisible by 3, 5, 7.

**The "Factor Pump" Mechanism:**
We identify a feedback loop that drives the accumulation of factors:

1.  **Input:** $a_k$ has many prime factors with odd exponents.
2.  **Parity Transformation:** $\sigma(p^e)$ is even iff $e$ is odd. Each such factor contributes at least one factor of 2 to $\sigma(a_k) = a_{k+1}$.
    - $v_2(a_{k+1}) = \sum_{p|a_k, e_p \text{ odd}} v_2(\sigma(p^{e_p}))$.
    - More distinct prime factors $\implies$ Higher $v_2(a_{k+1})$ (likely).
3.  **Output:** $a_{k+1}$ is even with high 2-valuation $m = v_2(a_{k+1})$.
4.  **New Factors:** In the next step, $a_{k+2} = \sigma(a_{k+1})$.
    - Since $a_{k+1} = 2^m \cdot d$, $\sigma(a_{k+1}) = (2^{m+1}-1) \sigma(d)$.
    - The term $2^{m+1}-1$ introduces new prime factors.
    - If $m$ is composite, $2^{m+1}-1$ has algebraic factors (e.g., $2^x-1$).
    - $\omega(2^n-1) \ge \omega(n)$.
    - So a large $v_2(a_{k+1})$ generates many factors in $a_{k+2}$.

**Conclusion:**
"Thin" even terms (where $R_k \approx 1.5$) correspond to cases where this pump fails (e.g., $v_2(a_k)$ is small, or $2^{v_2+1}-1$ is a Mersenne prime).
However, since $v_2(a_k)$ tends to grow (or at least fluctuate high), these "thin" events should be sparse.
Specifically, if $v_2(a_k)$ is large, $a_{k+1}$ cannot be "thin".

## 3. Strategy for Density-Based Proof

1.  **Assume Eventual Even Stability:** Work with the skeleton where $a_k$ is always even.
2.  **Define "Thickness":** Let $T(a_k) = \sum_{p|a_k} \frac{1}{p}$. We need $T(a_k)$ to be large on average.
3.  **Analyze 2-Valuation:** Study the dynamics of $v_2(a_k)$.
    - Show that $v_2(a_k)$ is not bounded, or frequently large.
    - Use the relation $v_2(a_{k+1}) \approx \omega_{odd}(a_k)$ (heuristic).
4.  **Connect to Growth:**
    - large $\omega(a_k) \implies$ large $v_2(a_{k+1}) \implies$ large $\omega(a_{k+2})$.
    - This suggests $\omega(a_k)$ grows, hence $R_k$ grows.
5.  **Handle Sparsity:**
    - Even if "Mersenne Wipeouts" occur (resetting $\omega$ to small value), the growth rate of $\omega$ (logarithmic or better) combined with the rarity of Mersenne primes ensures the *average* $\log R_k$ remains high.

## 4. Formalize Task
Create a task to formalize the "Factor Pump" argument: specifically, that $v_2(\sigma(n))$ relates to $\omega(n)$, and $\omega(\sigma(2^m d))$ relates to factorization of $2^{m+1}-1$.
