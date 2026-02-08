# Dead Ends — Approaches That Don't Work

This file records approaches that have been thoroughly analyzed and found to be mathematically insufficient or repeatedly failed. **Do not re-attempt these approaches.**

---

## Dead End 1: Lim Sup of Ratios (Analyzed 2026-02-08)

**Approach:** Replace the sorry `Tendsto (σ(aₖ₊₁)/aₖ) atTop atTop` with the weaker `limsup σ(aₖ)/aₖ = ∞`, i.e., for any M, there exist infinitely many k with σ(aₖ)/aₖ > M.

**Why it fails:** The theorem requires `aₖ^{1/k} → ∞`, which is equivalent to `(1/k) ∑_{j<k} log(Rⱼ) → ∞` where `Rⱼ = σ(aⱼ)/aⱼ`. This is the **Cesàro mean** of `log Rⱼ`.

Lim sup Rₖ = ∞ only guarantees infinitely many large values of Rₖ, but says nothing about the average. Counterexample: if Rₖ = k when k is a perfect square, and Rₖ = 3/2 otherwise, then lim sup = ∞ but the Cesàro mean of log Rₖ → log(3/2) (bounded). So `aₖ^{1/k}` stays bounded.

The current proof chain (ratio → ∞ ⟹ eventually ratio ≥ C ⟹ geometric growth ⟹ C^k bound) **fundamentally requires the full limit**, not lim sup. The "eventually" step needs: ∀ C > 1, ∃ K, **∀** k ≥ K, Rₖ ≥ C. Lim sup only gives: ∀ C > 1, ∃ **infinitely many** k with Rₖ ≥ C.

**Between spikes, consecutive C-multiplications cannot be chained**, so the geometric growth argument collapses. Even with the floor Rₖ ≥ 3/2 (from even terms), the baseline growth rate of (3/2)^k only gives aₖ^{1/k} → 3/2 (bounded).

**Conclusion:** No Lean skeleton using only lim sup σ(aₖ)/aₖ = ∞ can prove the theorem. The full limit is necessary for the current proof structure, and no alternative structure has been found that avoids it.

---

## Dead End 2: ω(aₖ) → ∞ via Persistence (3 attempts, rejected)

**Approach:** Prove that the number of distinct prime factors ω(aₖ) → ∞ by showing individual primes persist in the sequence (via Zsygmondy recurrence).

**Why it fails:** The "persistence trap." Showing a prime *enters* the orbit is easy (Zsygmondy), but showing it *stays* requires controlling the entire σ dynamics. All three proof attempts (omega-divergence.md, ratio-divergence.md, ratio-divergence-v2.md) fell into this trap: claiming that Zsygmondy primes with periodic recurrence conditions are simultaneously present, without justifying that the sequence achieves the needed exponent alignments.

**Specific recurring gaps:**
- Claiming v₂(aₖ) hits every residue class (unboundedness ≠ equidistribution)
- Claiming multiple primes are simultaneously present (alignment trap)
- Hand-waving about Chebotarev density in deterministic sequences

---

## Dead End 3: σ(m) ≥ m^{1+δ} for Large m

**Approach:** Show σ(m) grows polynomially faster than m, giving double-exponential growth.

**Why it fails:** The opposite is true. By Robin's inequality / Grönwall's theorem, σ(m)/m = O(log log m) for most m. So σ(m) ≤ m · O(log log m) ≪ m^{1+δ} for any δ > 0. The ratio σ(m)/m grows only logarithmically (in log log m), not polynomially.

---

## Dead End 4: Smooth Escape Alone ⟹ aₖ^{1/k} → ∞

**Approach:** Use the verified smooth escape result (σ-orbit escapes every finite smooth set) to directly conclude super-exponential growth.

**Why it fails:** Smooth escape says: for any finite set S of primes, a_k has prime factors outside S infinitely often. This means the prime support is infinite, but says nothing about multiplicative growth rates. A sequence can escape every smooth set while growing only polynomially. Counterexample (abstract): a_k = 2^k · p_k where p_k is the k-th prime. Then a_k^{1/k} → 2 (bounded) but the orbit is never eventually S-smooth.

---

## Dead End 5: ω Unbounded (lim sup) ⟹ σ(aₖ)/aₖ → ∞

**Approach:** Use lim sup ω(aₖ) = ∞ to conclude the abundancy ratio diverges.

**Why it fails:** Even ω(aₖ) → ∞ (full limit) does NOT imply σ(aₖ)/aₖ → ∞ unless the primes are small. If ω(aₖ) → ∞ with all extra primes very large (say > aₖ^{1/ω}), then ∏(1+1/p) converges. The product diverges only when the reciprocal sum ∑_{p|aₖ} 1/p → ∞, which requires many SMALL primes.

For the specific orbit, we expect small primes (2, 3, 7, ...) to appear frequently via the Mersenne mechanism, but proving this rigorously hits the persistence/alignment trap (Dead End 2).

---

## Dead End 6: Bounded-Ratio Contradiction via Smooth Escape

**Approach:** Assume liminf σ(aₖ)/aₖ < ∞, extract a bounded-ratio subsequence, show these terms must be eventually S-smooth for some finite S, contradicting the smooth escape theorem.

**Why it fails:** The bounded-ratio constraint (σ(m)/m ≤ C implies ω(m) ≤ D√(log m)) constrains the structure of each *individual* term but NOT which primes appear *across* the subsequence. Different low-ratio steps can have entirely different (finite) sets of primes. Smooth escape and liminf R_k < ∞ are COMPATIBLE: the orbit can oscillate between simple (low-ratio, few primes) and complex (high-ratio, many primes) configurations. The "finiteness of D-element prime sets meeting the orbit" argument fails because the number of possible D-element subsets grows without bound as the terms grow.
