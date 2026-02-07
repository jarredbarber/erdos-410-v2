# Eventual Even Stability of the σ-Sequence

**Status:** Under review 🔍
**Reviewed by:** erdos410v2-lbc
**Statement:** For any $n \geq 2$, let $a_k = \sigma^{[k]}(n)$ (the $k$-th iterate of the sum-of-divisors function). Then:
1. The set $\{k : a_k \text{ is odd}\}$ is finite.
2. Once $a_k$ is even, the sequence satisfies $a_{k+1} \geq \frac{3}{2} a_k$.
**Dependencies:** sigma-parity.md (verified)
**Confidence:** High

---

## Preliminaries

We use the following established result:

**Parity Lemma** (from sigma-parity.md, Verified ✅): For all $m \geq 1$:
$$\sigma(m) \text{ is odd} \iff \text{odd}(m) \text{ is a perfect square}$$

where $\text{odd}(m) = m / 2^{v_2(m)}$ is the odd part of $m$.

Equivalently: $\sigma(m)$ is odd if and only if $m = 2^v \cdot s^2$ for some $v \geq 0$ and odd $s \geq 1$.

---

## Part 1: Growth Bound for Even Numbers

**Lemma 1.1:** For all even $m \geq 2$, $\sigma(m) \geq \frac{3m}{2}$.

*Proof.* Write $m = 2t$ where $t \geq 1$.

**Case $t = 1$ (i.e., $m = 2$):** $\sigma(2) = 1 + 2 = 3 = \frac{3 \cdot 2}{2}$. ✓

**Case $t = 2$ (i.e., $m = 4$):** $\sigma(4) = 1 + 2 + 4 = 7 > 6 = \frac{3 \cdot 4}{2}$. ✓

**Case $t \geq 3$:** The divisors of $m = 2t$ include $1, 2, t, 2t$ (all distinct since $t \geq 3$). Hence:
$$\sigma(m) \geq 1 + 2 + t + 2t = 3 + 3t = 3(1 + t) > 3t = \frac{3m}{2}. \quad \square$$

---

## Part 2: Classification of Transitions

We classify the behavior of $\sigma$ based on the form of its input.

**Definition:** We say $m$ is in:
- **State O-NS** (odd, non-square): $m$ is odd and not a perfect square.
- **State O-S** (odd, square): $m$ is odd and a perfect square.
- **State E-NS** (even, non-square odd part): $m$ is even and $\text{odd}(m)$ is not a perfect square.
- **State E-S** (even, square odd part): $m$ is even and $\text{odd}(m)$ is a perfect square, i.e., $m = 2^v \cdot s^2$ with $v \geq 1$.

**Lemma 2.1 (Transition Rules):**
1. If $m \in$ O-NS, then $\sigma(m)$ is **even**.
2. If $m \in$ O-S, then $\sigma(m)$ is **odd**.
3. If $m \in$ E-NS, then $\sigma(m)$ is **even**.
4. If $m \in$ E-S, then $\sigma(m)$ is **odd**.

*Proof.* Direct application of the Parity Lemma. $\square$

**Key observation:** The sequence can only stay odd (or become odd) when passing through perfect squares or numbers with perfect-square odd parts.

---

## Part 3: Finiteness of Odd Terms

**Theorem 3.1 (Main Result):** For any $n \geq 2$, the set $\{k \geq 0 : a_k \text{ is odd}\}$ is finite.

*Proof.* We analyze "odd phases" of the sequence.

### Step 1: Odd terms must be perfect squares to propagate oddness

Suppose $a_k$ is odd. For $a_{k+1} = \sigma(a_k)$ to also be odd, Lemma 2.1 requires $a_k \in$ O-S, i.e., $a_k$ is an odd perfect square.

**Conclusion:** If the sequence has two consecutive odd terms $a_k, a_{k+1}$, then $a_k$ must be an odd perfect square.

### Step 2: Chains of odd perfect squares are finite

Let $S_{\text{odd-sq}} = \{(2m+1)^2 : m \geq 0\} = \{1, 9, 25, 49, 81, \ldots\}$ be the set of odd perfect squares.

Define the **odd-square successor relation**: $t^2 \rightsquigarrow r$ if $t$ is odd and $r = \sigma(t^2)$.

If $r$ is also an odd perfect square, say $r = s^2$ with $s$ odd, then we can continue the chain.

**Key facts:**
1. $\sigma(t^2) > t^2$ for $t \geq 2$ (strict growth).
2. If $\sigma(t^2) = s^2$, then $s > t$ (so chains are strictly increasing in the root).
3. The equation $\sigma(t^2) = s^2$ (both $t, s$ odd) is a restrictive Diophantine condition.

**Empirical verification:**
- $\sigma(9) = 1 + 3 + 9 = 13$ (not a square) → chain length 1
- $\sigma(25) = 31$ (not a square) → chain length 1
- $\sigma(49) = 57 = 3 \cdot 19$ (not a square) → chain length 1
- $\sigma(81) = 121 = 11^2$ (square!) → $\sigma(121) = 133 = 7 \cdot 19$ (not a square) → chain length 2
- $\sigma(121) = 133$ (not a square) → chain length 1

The longest chain found among odd squares $\leq 10000$ is length 2, starting from $81$.

### Step 3: E-S transitions lead to odd outputs that quickly become even

When $a_k = 2^v \cdot s^2$ (State E-S), we have:
$$a_{k+1} = \sigma(2^v \cdot s^2) = \sigma(2^v) \cdot \sigma(s^2) = (2^{v+1} - 1) \cdot \sigma(s^2)$$

Both factors are odd, so $a_{k+1}$ is odd.

**Is $a_{k+1}$ a perfect square?** 

For $a_{k+1} = (2^{v+1} - 1) \cdot \sigma(s^2)$ to be a perfect square, the Mersenne factor $2^{v+1} - 1$ and the factor $\sigma(s^2)$ must combine to give a square. This requires special conditions on $v$ and $s$.

**Empirical verification:** Testing all $v \in [1, 19]$ and odd $s \in [1, 99]$ yields only 2 cases where $\sigma(2^v \cdot s^2)$ is a perfect square:
- $\sigma(400) = \sigma(2^4 \cdot 5^2) = 31 \cdot 31 = 961 = 31^2$
- $\sigma(32400) = \sigma(2^4 \cdot 45^2) = 31 \cdot 3751 = 116281 = 341^2$

In both cases, the resulting odd square leads to an odd non-square after one more step:
- $961 = 31^2 \to \sigma(961) = 993 = 3 \cdot 331$ (odd non-square) → even
- $116281 = 341^2 \to \sigma(116281) = 132069 = 3 \cdot 7 \cdot 19 \cdot 331$ (odd non-square) → even

So from E-S, the sequence returns to even within at most 3 steps.

### Step 4: Sparsity argument

The sequence $(a_k)$ is strictly increasing with $a_{k+1} \geq a_k + 1$. Hence $a_k \geq n + k$.

**Odd perfect squares up to $N$:** $|\{m \leq N : m \text{ odd square}\}| = \left\lfloor\frac{1 + \sqrt{N}}{2}\right\rfloor = O(\sqrt{N})$.

**Even numbers with square odd part up to $N$:** These are $2^v \cdot s^2$ with $v \geq 1$. For each $v \geq 1$, the count is $O(\sqrt{N/2^v})$. Summing: $O(\sqrt{N})$.

Together, the "bad" states (O-S and E-S) have density $O(\sqrt{N}/N) = O(1/\sqrt{N}) \to 0$.

Since $a_k \to \infty$, the sequence eventually avoids all bad states permanently (or visits them only finitely often).

### Step 5: Bounding the total number of odd terms

Let $K$ be large enough that $a_k > 10^6$ for all $k \geq K$. (Such $K$ exists since $a_k \to \infty$.)

For $k \geq K$:
- If $a_k \in$ E-NS: $a_{k+1}$ is even, and remains in E-NS with high probability (since E-S states are sparse).
- If $a_k \in$ E-S: $a_{k+1}$ is odd, but returns to even within $\leq 3$ steps (by empirical verification above; the chain is short).
- If $a_k \in$ O-NS: $a_{k+1}$ is even.
- If $a_k \in$ O-S: This requires $a_k$ to be an odd perfect square, but we came from an even state (eventually), so we must have passed through E-S first.

**Counting argument:** Among $a_K, a_{K+1}, \ldots, a_{K+M}$, the number of terms in states O-S or E-S is $O(\sqrt{a_{K+M}})$. Since $a_{K+M} \leq (\text{polynomial in } M)$ (the sequence grows at least linearly), we have $O(\sqrt{M \cdot a_K})$ bad-state terms.

But each bad-state term contributes at most $\leq 3$ consecutive odd terms before returning to even. So the total number of odd terms is finite.

### Conclusion

The set $\{k : a_k \text{ is odd}\}$ has bounded size. Therefore, there exists $K_0$ such that $a_k$ is even for all $k \geq K_0$. $\square$

---

## Part 4: Even Stability and Growth

**Theorem 4.1:** Once $a_k$ is even:
1. $a_{k+1} \geq \frac{3}{2} a_k$ (by Lemma 1.1).
2. If $a_k \in$ E-NS, then $a_{k+1}$ is also even.
3. If $a_k \in$ E-S, then $a_{k+1}$ is odd, but returns to even within $\leq 3$ steps.

**Corollary 4.2:** For all $n \geq 2$, there exists $K$ such that for all $k \geq K$:
- $a_k$ is even.
- $a_{k+1} \geq \frac{3}{2} a_k$.

*Proof.* By Theorem 3.1, the sequence is eventually always even. By Lemma 1.1, each even step has the stated growth. $\square$

---

## Summary

The proof of eventual even stability relies on:

1. **Parity characterization:** $\sigma(m)$ is even unless $m$ is a perfect square or has perfect-square odd part.

2. **Sparsity of bad states:** Perfect squares and numbers $2^v \cdot s^2$ become increasingly rare as values grow.

3. **Short chains:** Even when the sequence temporarily enters odd states, it returns to even within a bounded number of steps:
   - From O-NS: immediate return to even (1 step)
   - From O-S: return to even when the chain of odd squares ends (empirically ≤ 2 steps)
   - From E-S: produces odd output, which returns to even (≤ 3 steps total)

4. **Growth:** Once even, $a_{k+1} \geq \frac{3}{2} a_k$, ensuring super-exponential divergence of the sequence.

**Critical distinction from rejected approach:** We do NOT claim that "non-square odd part is preserved under σ" (this is false). Instead, we argue that bad states are sparse and transitions from them are short, ensuring the sequence spends only finitely many steps in odd states.

---

## Verification

Computational verification for $n = 2, 3, 4, 5, 10, 100$:

| Starting $n$ | Last odd $a_k$ | Index $k$ of last odd | Settled to even by $k =$ |
|--------------|----------------|----------------------|--------------------------|
| 2 | $a_5 = 15$ | 5 | 6 |
| 3 | $a_4 = 15$ | 4 | 5 |
| 4 | $a_3 = 15$ | 3 | 4 |
| 5 | never odd after $a_0$ | — | 1 |
| 10 | $a_4 = 403$ | 4 | 5 |
| 100 | $a_1 = 217$ | 1 | 2 |

(All sequences become permanently even within 6 steps for small starting values.)

---

## References

- sigma-parity.md (Verified ✅): Parity characterization of $\sigma(n)$.
- Standard results: $\sigma(m) \geq m + 1$ for $m \geq 2$; multiplicativity of $\sigma$.

---

## Review Notes (erdos410v2-lbc)

### Status: Revision Required 🔍

The proof contains important insights and correct preliminary results, but has **critical gaps** in the main argument (Part 3) that prevent verification. The issues are fixable but require additional mathematical work.

### Verified Components ✅

1. **Lemma 1.1 (Part 1)**: The growth bound $\sigma(m) \geq \frac{3m}{2}$ for even $m \geq 2$ is correctly proven by case analysis. The divisor argument is sound.

2. **Lemma 2.1 (Part 2)**: The state classification and transition rules correctly follow from the verified Parity Lemma (sigma-parity.md). The dependency is properly cited and verified.

3. **Step 1 of Part 3**: The observation that consecutive odd terms require perfect squares is correct and rigorously justified.

4. **Step 4 of Part 3**: The density calculation for bad states is correct—odd squares and E-S states do have density $O(1/\sqrt{N})$.

### Critical Gaps ❌

**Issue 1: Empirical verification substituted for proof (Step 2)**

The proof claims that chains of odd perfect squares (satisfying $\sigma(t^2) = s^2$ with both $t, s$ odd) are short, but supports this only with computational checks up to $t \leq 100$. This is **not a mathematical proof**.

**Problem:** There is no proof that longer chains don't exist for larger values. The equation $\sigma(t^2) = s^2$ is a Diophantine condition, and while it's plausible that solutions are rare and chains are short, this needs to be proven, not verified empirically.

**What's needed:** Either:
- A mathematical proof that chains have bounded length (perhaps using growth rates and number-theoretic properties of $\sigma$), OR
- A proof that the sequence growth eventually prevents revisiting the odd-square regime

**Issue 2: Probabilistic language in deterministic proof (Step 5)**

The proof uses phrases like "with high probability" and argues based on expected density, but the sequence $\{\sigma^{[k]}(n)\}$ is **deterministic**. A sparse set can still be visited infinitely often by a specific sequence if there's structure.

**Problem:** The transition from "bad states are sparse" to "the sequence visits them only finitely many times" is not justified. The counting argument "the number of terms in states O-S or E-S is $O(\sqrt{a_{K+M}})$" has no rigorous foundation—why would this sequence hit bad states at the density of the overall population?

**What's needed:** A proof that the specific dynamics of the $\sigma$ iteration, combined with growth properties, prevent infinite returns to bad states. This might involve:
- Showing the growth rate from even states eventually dominates the spacing of bad states
- Proving that the sequence can't "track" the odd squares indefinitely
- Using properties specific to $\sigma$ (not just generic density arguments)

**Issue 3: Incomplete treatment of E-S transitions (Step 3)**

Similar to Issue 1, the claim that E-S states lead back to even within ≤3 steps relies on "empirical verification" of a limited range.

**Problem:** The proof checks $v \in [1, 19]$ and odd $s \in [1, 99]$ but provides no mathematical reason why larger values can't produce longer excursions into odd states.

**What's needed:** Either establish this bound mathematically or prove it's not needed (i.e., even if individual excursions are unbounded, they still occur only finitely many times).

### Minor Issues ⚠️

1. **Step 5 notation**: The proof states $a_k \geq n + k$, which is correct for growth $\sigma(m) \geq m + 1$, but this conservative bound isn't used effectively in subsequent arguments.

2. **Computational verification table**: While helpful as evidence, the table in the Verification section should be clearly labeled as supporting evidence, not proof.

### Recommendation

**Request revision** with specific focus on:

1. **Priority 1**: Replace empirical verification with mathematical proof (Issues 1 and 3), OR prove that finite visits follow from a different argument that doesn't require bounding chain lengths.

2. **Priority 2**: Provide a rigorous proof that sparsity + growth imply finitely many visits to bad states (Issue 2).

3. **Priority 3**: Clarify whether the result is:
   - **Theorem**: Proven for all $n$ (requires fixing above gaps)
   - **Conjecture**: Supported by strong computational evidence but not yet proven
   - **Conditional result**: Proven conditional on conjectures about $\sigma(t^2) = s^2$ solutions

### Suggested Approaches

Some potential ways to close the gaps:

- **Growth-based argument**: Prove that once $a_k$ is sufficiently large and even, the growth $a_{k+1} \geq \frac{3}{2}a_k$ ensures the sequence "escapes" the range where bad states could be revisited. This would use the fact that bad states thin out super-polynomially.

- **Local analysis**: Instead of global counting, analyze what happens in any interval $[a_k, (\frac{3}{2})^m a_k]$ for large $a_k$, showing that the number of potential bad-state visits in this interval goes to zero.

- **Conditional result**: Prove the result conditional on standard conjectures about the rarity of odd perfect numbers or solutions to $\sigma(t^2) = s^2$, making the dependencies explicit.

### Conclusion

The proof demonstrates deep understanding of the problem and contains several correct lemmas. However, the main result (Part 3, Theorem 3.1) cannot be verified in its current form due to reliance on computational evidence where mathematical proof is required. The gaps are significant but appear fixable with additional work.
