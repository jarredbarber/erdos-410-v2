# Super-Exponential Growth of Iterated Sum-of-Divisors (Assembly)

**Status:** Under review 🔍
**Reviewed by:** erdos410v2-xlm
**Statement:** For all $n \geq 2$,
$$\lim_{k \to \infty} \sigma^{[k]}(n)^{1/k} = \infty,$$
where $\sigma^{[k]}$ denotes the $k$-th iterate of the sum-of-divisors function.
**Dependencies:**
- sigma-lower-bounds.md (Verified ✅) — Bound 1: $\sigma(m) \geq m + 1$ for $m \geq 2$
- **ratio-divergence.md (Rejected ❌)** — $\sigma(a_k)/a_k \to \infty$. ⚠️ This dependency is NOT currently verified. The assembly argument below is rigorous *conditional* on ratio divergence being established. See §Critical Dependency Gap.
**Confidence:** Certain (for the assembly logic itself); the proof is complete modulo the ratio-divergence input.

---

## Notation

Let $n \geq 2$ be a fixed integer. Define the sequence:
- $a_0 = n$
- $a_{k+1} = \sigma(a_k)$ for $k \geq 0$

where $\sigma(m) = \sum_{d \mid m} d$ is the sum of all positive divisors of $m$.

We write $R_k = \sigma(a_k)/a_k = a_{k+1}/a_k$ for the growth ratio at step $k$.

---

## Component Results

We use exactly two inputs:

**Result A** (sigma-lower-bounds.md, Verified ✅): For all $m \geq 2$, $\sigma(m) \geq m + 1$.

**Result B** (ratio-divergence — see dependency note above): For any $n \geq 2$, with $a_k = \sigma^{[k]}(n)$,
$$\lim_{k \to \infty} \frac{\sigma(a_k)}{a_k} = +\infty.$$

That is, $R_k \to +\infty$.

---

## Proof

### Step 0: The sequence is well-defined and diverges

Since $a_0 = n \geq 2$ and $\sigma(m) \geq m + 1 > m$ for all $m \geq 2$ (Result A), an immediate induction gives:
- $a_k \geq 2$ for all $k \geq 0$.
- $a_{k+1} > a_k$ for all $k \geq 0$ (strict monotonicity).
- $a_k \geq n + k \to \infty$ (divergence).

In particular, the ratio $R_k = a_{k+1}/a_k$ is well-defined and satisfies $R_k > 1$ for all $k$.

### Step 1: Ratio divergence implies eventual domination by any constant

Let $C > 1$ be arbitrary.

By Result B, $R_k \to +\infty$. In particular, $R_k > C$ for all sufficiently large $k$. That is, there exists $K = K(C, n) \in \mathbb{N}$ such that

$$R_k = \frac{a_{k+1}}{a_k} > C \quad \text{for all } k \geq K.$$

### Step 2: Geometric growth past the threshold

For all $k \geq K$, we have $a_{k+1} > C \cdot a_k$. By induction on $j \geq 0$:

**Base case** ($j = 0$): $a_K = C^0 \cdot a_K$. ✓

**Inductive step**: Suppose $a_{K+j} > C^j \cdot a_K$. Then:
$$a_{K+j+1} > C \cdot a_{K+j} > C \cdot C^j \cdot a_K = C^{j+1} \cdot a_K.$$

Therefore, for all $j \geq 0$:

$$a_{K+j} \geq C^j \cdot a_K.$$

(With strict inequality for $j \geq 1$.)

### Step 3: Extracting the $k$-th root

For $k \geq K$, set $j = k - K \geq 0$. Then:

$$a_k \geq C^{k-K} \cdot a_K = \frac{a_K}{C^K} \cdot C^k.$$

Taking $k$-th roots (all quantities are positive):

$$a_k^{1/k} \geq \left(\frac{a_K}{C^K}\right)^{1/k} \cdot C.$$

### Step 4: Taking the limit

The quantity $a_K / C^K$ is a fixed positive constant (depending on $C$ and $n$, but not on $k$). Therefore:

$$\left(\frac{a_K}{C^K}\right)^{1/k} \to 1 \quad \text{as } k \to \infty,$$

since $x^{1/k} \to 1$ for any fixed $x > 0$. (Proof: $\log(x^{1/k}) = (\log x)/k \to 0$.)

Hence:

$$\liminf_{k \to \infty} a_k^{1/k} \geq \lim_{k \to \infty} \left(\frac{a_K}{C^K}\right)^{1/k} \cdot C = 1 \cdot C = C.$$

### Step 5: Conclusion

Since $C > 1$ was arbitrary, we have $\liminf_{k \to \infty} a_k^{1/k} \geq C$ for every $C > 1$. Therefore:

$$\liminf_{k \to \infty} a_k^{1/k} = +\infty,$$

which implies

$$\lim_{k \to \infty} a_k^{1/k} = +\infty.$$

(The liminf being $+\infty$ is equivalent to the limit being $+\infty$, since every subsequence is bounded below by the liminf.) $\square$

---

## Critical Dependency Gap

⚠️ **Result B (ratio divergence) is not currently verified.**

The file `proofs/ratio-divergence.md` was **Rejected ❌** during review. The rejection identified critical gaps in the proof's Case B, specifically:

1. **Residue class hitting**: The claim that $v_2(a_k) + 1$ hits every residue class modulo $d$ (for arbitrary $d$) is unjustified. Unboundedness of $v_2(a_k)$ does not imply this.

2. **Multiplicative order control**: No rigorous justification for controlling which prime achieves the maximum exponent at a given step.

The assembly argument presented above (Steps 0–5) is **completely rigorous** and introduces no gaps of its own. The entire proof of Erdős #410 reduces to establishing Result B.

**Recommendation**: Result B should be established via a new proof approach. The hints in `proofs/hints.md` suggest an energy/potential function argument that avoids tracking individual primes and instead works directly with the abundancy ratio $\sigma(m)/m$, exploiting the multiplicative formula $\sigma(m)/m = \prod_{p^a \| m} (1 + 1/p + \cdots + 1/p^a)$ and the growth of exponents as $a_k \to \infty$.

---

## References

- **sigma-lower-bounds.md** (Verified ✅): Basic lower bounds for $\sigma(n)$, specifically $\sigma(n) \geq n + 1$ for $n \geq 2$.
- **ratio-divergence.md** (Rejected ❌): Attempted proof that $\sigma(a_k)/a_k \to \infty$. The claim is used here but not yet established.

---

## Review Notes (erdos410v2-xlm)

**CONDITIONAL APPROVAL** — The assembly logic (Steps 0-5) is mathematically rigorous and correct. However, this proof cannot advance to **Verified ✅** status until its critical dependency is established.

### Assessment Against Review Criteria

✅ **Statement clarity**: The theorem statement is precise and matches the Lean formalization (`∀ n > 1, Tendsto (fun k ↦ (σ^{[k]}(n) : ℝ)^{1/k}) atTop atTop`).

✅ **Assumptions**: All assumptions are stated explicitly. The proof is transparent about being conditional on Result B.

✅ **Logical flow**: Each step in the assembly argument (Steps 0-5) follows logically from the previous.

✅ **Quantifiers**: Correctly used throughout. The argument with arbitrary $C > 1$ in Step 1 is sound.

✅ **Edge cases**: The base case ($a_0 = n \geq 2$) and the induction in Step 2 are handled correctly.

❌ **Dependencies**: The proof cites **ratio-divergence.md**, which has status **Rejected ❌**. This is a blocking issue.

✅ **Completeness**: The proof DOES prove the stated result, conditional on Result B (ratio divergence).

✅ **Hidden assumptions**: None. The dependency on Result B is explicitly acknowledged.

### Detailed Analysis

**The Assembly Logic Is Sound:**

1. **Step 0** (sequence well-defined): Uses only sigma-lower-bounds.md (Verified ✅). Rigorous. ✓

2. **Step 1** (ratio divergence implies eventual domination): ASSUMES Result B, then correctly derives that $R_k > C$ eventually. The logical inference is valid. ✓

3. **Step 2** (geometric growth past threshold): The induction proof that $a_{K+j} \geq C^j \cdot a_K$ for all $j \geq 0$ is completely rigorous. ✓

4. **Step 3** (extracting k-th root): The algebraic manipulation is correct. ✓

5. **Step 4** (taking the limit): The limit $\left(\frac{a_K}{C^K}\right)^{1/k} \to 1$ is justified by $\log(x^{1/k}) = (\log x)/k \to 0$ for fixed $x > 0$. Correct. ✓

6. **Step 5** (conclusion): The argument that $\liminf_{k \to \infty} a_k^{1/k} \geq C$ for arbitrary $C > 1$ implies $\lim_{k \to \infty} a_k^{1/k} = +\infty$ is valid. ✓

**No gaps were found in the assembly logic.** The proof achieves what it claims: a reduction of Erdős #410 to the ratio divergence result.

### Critical Dependency Gap

The proof depends on **Result B**: For any $n \geq 2$, $\lim_{k \to \infty} \frac{\sigma(a_k)}{a_k} = +\infty$.

**Current status of Result B**: The file `proofs/ratio-divergence.md` attempted to prove this but was **Rejected ❌** by review erdos410v2-i9u due to critical gaps:
- Unjustified residue class hitting claim
- Lack of control over which primes achieve maximum exponents  
- Hand-waving about Chebotarev density

The review of ratio-divergence.md recommended: "A fundamentally different approach is needed rather than revision attempts," specifically suggesting an **energy/potential function** approach that tracks $\log(\sigma(a_k)/a_k)$ and proves it grows on average, without requiring control over which specific primes appear when.

### Verdict and Recommendations

**Status**: Keep at **Under review 🔍** (not Draft, not Verified).

**Blocking issue**: Cannot advance to **Verified ✅** until Result B is established.

**Recommended action**: Create a high-priority `explore` task to establish ratio divergence via the energy function approach suggested in the ratio-divergence.md review. Once that dependency is verified, this assembly proof can immediately be promoted to Verified ✅.

**Mathematical assessment**: The assembly proof is publication-ready conditional logic. It represents a successful reduction of the full Erdős #410 theorem to a single technical lemma (ratio divergence). This is valuable progress.

**Lean formalization readiness**: Once ratio-divergence is verified, this proof provides a clear blueprint for Lean formalization:
1. `lemma ratio_divergence`: Formalize Result B
2. `lemma geometric_growth_from_ratio`: Formalize Steps 1-2  
3. `theorem erdos_410`: Combine via Steps 3-5

The proof structure is clean and suitable for direct translation to Lean.
