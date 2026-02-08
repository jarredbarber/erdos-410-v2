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

**Update (2026-02-08):** Another attempt (ratio-divergence-energy-v2.md) used an energy function E(m) = log(σ(m)/m) and tried to show recovery from low-ratio configurations. While it rigorously proved R_k ≥ 2 eventually and showed one-step recovery from R_k = 2, it could not establish bounded recovery time for arbitrary thresholds L > 2. The proof explicitly admitted it only achieves lim sup, not lim, falling into this same dead end.

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

---

## Dead End 7: Energy Monotonicity via Recovery Dynamics (rejected 2026-02-08)

**Tried:** Define energy E(m) = log(σ(m)/m). Show that low-ratio configurations (R_k ≤ L) lead to structural recovery (R_{k+j} > L within bounded steps). Combined with lim sup R_k = ∞, this would force lim R_k = ∞.

**Failed because:** While the approach rigorously establishes:
- R_k ≥ 2 eventually (with at most one exception)
- One-step recovery: R_k ≤ 2 ⟹ R_{k+1} > 2
- Structural characterization: low ratio ⟹ odd part is prime power

It cannot prove **bounded recovery time** for arbitrary thresholds L > 2. The gap: when R_k ≤ L, the odd part m_k must be a prime power, and σ(m_k) typically has more prime factors, suggesting eventual recovery. But "typically" is not "always" (Mersenne primes exist), and more prime factors doesn't guarantee higher ratio if the new primes are large. The proof requires Conjecture 6.1 (bounded recovery time) which remains unproven. Without this, the proof only establishes lim sup = ∞, falling into Dead End #1.

---

## Dead End 8: Accumulation of Reciprocal Sum (rejected 2026-02-08)

**Tried:** Prove ∑_{p|a_k} 1/p → ∞ by arguing that new prime factors from Smooth Escape accumulate and decay to small primes (e.g., p → p+1), increasing the sum.

**Failed because:** The "Concentration" effect of 2^k counteracts the "Decay". The transition a_k = 2^e → a_{k+1} = σ(2^e) can map a high-sum configuration (e.g., h(2^e)=0.5) to a low-sum configuration (e.g., h(M_e) ≈ 0 if M_e is Mersenne). Simulation shows the sum h(a_k) fluctuating wildly (e.g., 1.17 → 0.08) rather than accumulating monotonically. The "average" gain argument fails because the dynamics can hit the "worst-case" loss scenarios repeatedly.
