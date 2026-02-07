# Basic Lower Bounds for σ(n)

**Status:** Verified ✅
**Reviewed by:** erdos410v2-5p8
**Statement:** Three lower bounds for the sum-of-divisors function:
1. For all $n \geq 2$: $\sigma(n) \geq n + 1$.
2. For composite $n \geq 4$ with smallest prime factor $d$: $\sigma(n) \geq n + d + n/d + 1$ when $n \neq d^2$; in general $\sigma(n) \geq n + \sqrt{n} + 1$; and when $n$ is not a prime square, $\sigma(n) \geq (\sqrt{n} + 1)^2$.
3. For even $n \geq 2$: $\sigma(n) \geq \frac{3n}{2}$.

**Dependencies:** None (self-contained, elementary)
**Confidence:** Certain

---

## Notation

Throughout, $\sigma(n) = \sum_{d \mid n} d$ denotes the sum of all positive divisors of $n$.

---

## Bound 1: $\sigma(n) \geq n + 1$ for all $n \geq 2$

**Lemma 1.1.** For all integers $n \geq 2$, $\sigma(n) \geq n + 1$.

*Proof.* For any positive integer $n$, both $1$ and $n$ are divisors of $n$. Since $n \geq 2$, these are distinct: $1 \neq n$. Therefore:

$$\sigma(n) = \sum_{d \mid n} d \geq 1 + n = n + 1.$$

$\square$

**Remark.** Equality $\sigma(n) = n + 1$ holds if and only if the only divisors of $n$ are $1$ and $n$ itself, i.e., $n$ is prime.

---

## Bound 2: Composite lower bound via smallest prime factor

**Setup.** Let $n \geq 4$ be composite, and let $d$ denote the smallest prime factor of $n$ (equivalently, the smallest divisor of $n$ with $d > 1$). Since $n$ is composite, $1 < d < n$.

**Lemma 2.1** (Smallest prime factor bound). $d \leq \sqrt{n}$.

*Proof.* Suppose for contradiction that $d > \sqrt{n}$. Since $d$ is the smallest prime factor of $n$, every prime factor $p$ of $n$ satisfies $p \geq d > \sqrt{n}$. If $n$ has at least two prime factors (counting multiplicity), say $n \geq p_1 \cdot p_2$ with $p_1, p_2 > \sqrt{n}$, then $n \geq p_1 \cdot p_2 > \sqrt{n} \cdot \sqrt{n} = n$, a contradiction. So $n$ has exactly one prime factor counted with multiplicity, i.e., $n = p$ for some prime $p$, contradicting the assumption that $n$ is composite. $\square$

**Lemma 2.2** (Four-divisor bound). Suppose $n \geq 4$ is composite and $n \neq d^2$ (where $d$ is the smallest prime factor of $n$). Then $1, d, n/d, n$ are four distinct divisors of $n$, and:

$$\sigma(n) \geq 1 + d + \frac{n}{d} + n = n + d + \frac{n}{d} + 1.$$

*Proof.* Since $d \mid n$, both $d$ and $n/d$ are positive divisors of $n$. We verify the four values $1, d, n/d, n$ are distinct:

- $1 < d$: because $d \geq 2$ (being a prime factor).
- $d < n/d$: since $d \leq \sqrt{n}$ by Lemma 2.1, we have $n/d \geq \sqrt{n} \geq d$. Equality $d = n/d$ holds iff $n = d^2$, which is excluded by hypothesis. So $d < n/d$.
- $n/d < n$: because $d > 1$.

Therefore $1 < d < n/d < n$, and these four values are pairwise distinct divisors of $n$. Since $\sigma(n)$ is the sum over all divisors:

$$\sigma(n) \geq 1 + d + \frac{n}{d} + n. \quad \square$$

**Corollary 2.3** (AM-GM refinement). Under the hypotheses of Lemma 2.2:

$$\sigma(n) \geq n + 2\sqrt{n} + 1 = \left(\sqrt{n} + 1\right)^2.$$

*Proof.* By AM-GM applied to the positive reals $d$ and $n/d$:

$$d + \frac{n}{d} \geq 2\sqrt{d \cdot \frac{n}{d}} = 2\sqrt{n}.$$

Substituting into the bound from Lemma 2.2:

$$\sigma(n) \geq n + d + \frac{n}{d} + 1 \geq n + 2\sqrt{n} + 1 = \left(\sqrt{n} + 1\right)^2. \quad \square$$

**Lemma 2.4** (Prime square case). If $n = p^2$ for a prime $p$, then:

$$\sigma(n) = 1 + p + p^2 = n + \sqrt{n} + 1.$$

*Proof.* The divisors of $p^2$ are exactly $1, p, p^2$. Hence:

$$\sigma(p^2) = 1 + p + p^2 = p^2 + p + 1 = n + \sqrt{n} + 1. \quad \square$$

**Remark on prime squares.** The stronger bound $\sigma(n) \geq (\sqrt{n} + 1)^2 = n + 2\sqrt{n} + 1$ fails for $n = p^2$:

$$\sigma(p^2) = n + \sqrt{n} + 1 < n + 2\sqrt{n} + 1 \quad \text{whenever } \sqrt{n} = p > 0.$$

For instance, $\sigma(4) = 7 < 9 = (2+1)^2$ and $\sigma(9) = 13 < 16 = (3+1)^2$.

**Theorem 2.5** (Uniform composite bound). For all composite $n \geq 4$:

$$\sigma(n) \geq n + \sqrt{n} + 1 > n + \sqrt{n}.$$

*Proof.* Let $d$ be the smallest prime factor of $n$.

**Case 1: $n \neq d^2$.** By Lemma 2.2 and Corollary 2.3, $\sigma(n) \geq n + 2\sqrt{n} + 1 \geq n + \sqrt{n} + 1$ (since $\sqrt{n} \geq \sqrt{4} = 2 \geq 0$).

**Case 2: $n = d^2$ (i.e., $n = p^2$ for a prime $p$).** By Lemma 2.4, $\sigma(n) = n + \sqrt{n} + 1$.

In both cases $\sigma(n) \geq n + \sqrt{n} + 1$. $\square$

---

## Bound 3: $\sigma(n) \geq \frac{3n}{2}$ for even $n \geq 2$

We give two proofs: an elementary one by divisor counting, and a structural one using multiplicativity.

### Proof A (Divisor counting)

**Theorem 3.1.** For all even $n \geq 2$, $\sigma(n) \geq \frac{3n}{2}$.

*Proof.* Write $n = 2t$ where $t = n/2 \geq 1$.

**Case $t = 1$ ($n = 2$):** $\sigma(2) = 1 + 2 = 3 = \frac{3 \cdot 2}{2}$. Equality holds. $\checkmark$

**Case $t = 2$ ($n = 4$):** $\sigma(4) = 1 + 2 + 4 = 7 > 6 = \frac{3 \cdot 4}{2}$. $\checkmark$

**Case $t \geq 3$ ($n \geq 6$):** The values $1, 2, t, 2t$ are four divisors of $n = 2t$, and they are pairwise distinct since $t \geq 3 > 2$:

$$1 < 2 < t < 2t = n.$$

(Here $2 < t$ because $t \geq 3$, and $t < 2t$ since $t > 0$.) Therefore:

$$\sigma(n) \geq 1 + 2 + t + 2t = 3 + 3t = 3(t + 1) = 3\left(\frac{n}{2} + 1\right) = \frac{3n}{2} + 3 > \frac{3n}{2}. \quad \square$$

### Proof B (Multiplicativity)

**Theorem 3.1 (alternative proof).** For all even $n \geq 2$, $\sigma(n) \geq \frac{3n}{2}$.

*Proof.* Write $n = 2^a \cdot m$ where $a \geq 1$ and $m$ is odd. By multiplicativity of $\sigma$:

$$\sigma(n) = \sigma(2^a) \cdot \sigma(m) = (2^{a+1} - 1) \cdot \sigma(m).$$

Since $m$ is a divisor of $m$, we have $\sigma(m) \geq m$. Therefore:

$$\sigma(n) \geq (2^{a+1} - 1) \cdot m.$$

We claim $(2^{a+1} - 1) \geq \frac{3}{2} \cdot 2^a$ for all $a \geq 1$. Indeed:

$$2^{a+1} - 1 \geq \frac{3}{2} \cdot 2^a \iff 2 \cdot 2^a - 1 \geq \frac{3}{2} \cdot 2^a \iff \frac{1}{2} \cdot 2^a \geq 1 \iff 2^{a-1} \geq 1,$$

which holds for all $a \geq 1$. Therefore:

$$\sigma(n) \geq (2^{a+1} - 1) \cdot m \geq \frac{3}{2} \cdot 2^a \cdot m = \frac{3}{2} \cdot n. \quad \square$$

**Remark.** Equality $\sigma(n) = \frac{3n}{2}$ holds if and only if both inequalities are tight: $\sigma(m) = m$ (i.e., $m = 1$) and $2^{a+1} - 1 = \frac{3}{2} \cdot 2^a$ (i.e., $a = 1$). So equality holds precisely at $n = 2$.

**Corollary 3.2** (Growth ratio for even numbers). For even $n \geq 2$:

$$\frac{\sigma(n)}{n} \geq \frac{3}{2},$$

with equality only at $n = 2$.

---

## Summary

| Bound | Hypothesis | Conclusion | Tight at |
|-------|-----------|------------|----------|
| (1) | $n \geq 2$ | $\sigma(n) \geq n + 1$ | $n$ prime |
| (2a) | $n \geq 4$ composite, not a prime square | $\sigma(n) \geq n + d + n/d + 1 \geq (\sqrt{n}+1)^2$ | — |
| (2b) | $n = p^2$, $p$ prime | $\sigma(n) = n + \sqrt{n} + 1$ | Always (exact) |
| (2c) | $n \geq 4$ composite (uniform) | $\sigma(n) \geq n + \sqrt{n} + 1$ | $n = p^2$ |
| (3) | $n \geq 2$ even | $\sigma(n) \geq 3n/2$ | $n = 2$ |

These bounds are used in the main proof of Erdős Problem #410 to establish that the iterated $\sigma$-sequence grows at least geometrically once it enters the even regime (Bound 3), and that composite numbers receive a significant multiplicative boost (Bound 2).

---

## References

None — all results are elementary and self-contained.
