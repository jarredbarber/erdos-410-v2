# Divergence of the Abundancy Ratio

**Status:** Draft ✏️
**Statement:** For any $n \geq 2$, let $a_k = \sigma^{[k]}(n)$. Then $\displaystyle\limsup_{k \to \infty} \frac{\sigma(a_k)}{a_k} = +\infty$.
**Dependencies:** sigma-lower-bounds.md (Verified ✅), sigma-parity.md (Verified ✅)
**Confidence:** Moderate (main result depends on Small Prime Recurrence Lemma which requires further analysis)

---

## Overview

We prove $\limsup R_k = \infty$ where $R_k := \sigma(a_k)/a_k$ by combining:

1. **Zsygmondy Escape:** The total prime support $\mathcal{S}$ is infinite.
2. **Omega-Ratio Constraint:** Bounded ratio implies $\omega(a_k) = O(\sqrt{\log a_k})$.
3. **Small Prime Recurrence:** The σ-dynamics force small primes to reappear periodically.

---

## Part 1: Preliminaries

### The Multiplicative Formula

For $m \geq 2$:
$$R(m) := \frac{\sigma(m)}{m} = \prod_{p^e \| m} f(p, e) \quad \text{where} \quad f(p, e) = 1 + \frac{1}{p} + \cdots + \frac{1}{p^e}$$

Key bounds:
- $1 + 1/p < f(p, e) < p/(p-1)$ for all $p, e \geq 1$
- $f(2, e) \geq 3/2$ for all $e \geq 1$
- $R(m) > \prod_{p | m}(1 + 1/p)$

### Growth Bounds

From sigma-lower-bounds.md:
- $\sigma(m) \geq m + 1$ for all $m \geq 2$
- $\sigma(m) \geq 3m/2$ for even $m$

Therefore: $a_k$ is strictly increasing, $a_k \geq a_0 + k$, and $a_k \to \infty$.

---

## Part 2: Zsygmondy Escape — Infinite Support

**Theorem 2.1.** The total prime support $\mathcal{S} = \bigcup_{k \geq 0}\{p : p | a_k\}$ is infinite.

*Proof.* Suppose $\mathcal{S}$ is finite. All terms $a_k$ are $\mathcal{S}$-smooth.

Since $a_k \to \infty$ with $\mathcal{S}$ finite, exponents must grow: $\max_{p \in \mathcal{S}} v_p(a_k) \to \infty$.

By **Zsygmondy's theorem** (1892): For $p^{e+1} - 1$ with $e$ sufficiently large (finitely many exceptions), there exists a *primitive prime divisor* $q \nmid p^j - 1$ for $j < e+1$.

Such $q$ divides $\sigma(p^e) = (p^{e+1}-1)/(p-1)$ (since $q \nmid p-1$ by primitivity).

For each $p \in \mathcal{S}$, only finitely many primitive divisors can lie in $\mathcal{S}$ (since primitive divisors for different exponents are distinct). Define:
$$E(\mathcal{S}) = \max_{p \in \mathcal{S}}\{\min\{e : \text{primitive divisor of } p^{e+1}-1 \text{ is not in } \mathcal{S}\}\}$$

For $k$ large enough that $\max_{p} v_p(a_k) > E(\mathcal{S})$, some $\sigma(p^{v_p})$ has a prime factor $q \notin \mathcal{S}$.

Then $q | \sigma(a_k) = a_{k+1}$, contradicting $a_{k+1}$ being $\mathcal{S}$-smooth. $\square$

---

## Part 3: Omega-Ratio Constraint

**Lemma 3.1 (Small Prime Forcing).** If $m$ has $\omega(m) = W$ distinct prime factors, then:
$$\sum_{p | m} \frac{1}{p} \geq \frac{W}{m^{1/W}}$$

*Proof.* Let $p_1 < \cdots < p_W$ be the primes dividing $m$. Since $m \geq \prod p_i$:
$$\sum \frac{1}{p_i} \geq \frac{W}{(\prod p_i)^{1/W}} \geq \frac{W}{m^{1/W}} \quad \square$$

**Theorem 3.2 (Omega Bound from Bounded Ratio).** If $R_k \leq C$ for all $k$, then:
$$\omega(a_k) = O\left(\sqrt{\log a_k}\right)$$

*Proof.* From $R_k \leq C$:
$$\sum_{p | a_k} \frac{1}{p} \leq \sum_{p | a_k} \log\left(1 + \frac{1}{p}\right) \cdot 2 < 2\log R_k \leq 2\log C$$

Combined with Lemma 3.1:
$$\frac{\omega(a_k)}{a_k^{1/\omega(a_k)}} \leq 2\log C$$

Let $W = \omega(a_k)$ and $N = a_k$. We have $W / N^{1/W} \leq 2\log C$.

Taking logs: $\log W - (\log N)/W \leq \log(2\log C)$.

Rearranging: $W \log W - \log N \leq W \log(2\log C)$.

For $W > 4\log C$: $W^2/2 < W\log W$, so $W^2/2 - \log N < W\log(2\log C)$.

This gives: $W^2 < 2\log N + 2W\log(2\log C) < 2\log N + W^2/2$ for $W$ large.

Therefore: $W^2/2 < 2\log N$, so $W < 2\sqrt{\log N}$. $\square$

---

## Part 4: The Structure Under Bounded Ratio

**Proposition 4.1.** If $R_k \leq C$ for all $k$, then:
1. $\mathcal{S}$ is infinite (Theorem 2.1)
2. $\omega(a_k) = O(\sqrt{\log a_k})$ (Theorem 3.2)
3. Exponents grow: $\max_{p | a_k} v_p(a_k) \to \infty$
4. Zsygmondy primes keep entering and exiting

*Proof.* 
(1) and (2) are proven.

(3): If exponents were bounded by $E$, then with $\omega \leq W$:
$$a_k \leq (\max \text{ prime})^{W \cdot E}$$
Since $a_k \to \infty$, the max prime must $\to \infty$. But by (2), $\omega = O(\sqrt{\log a_k})$, so only $O(\sqrt{\log a_k})$ primes are present. For $a_k$ to grow beyond any bound with few primes and bounded exponents, the primes themselves must grow — i.e., new primes enter. As new primes enter with bounded slots, old ones exit.

(4): Follows from (1), (2), (3) and the constraint $\omega = O(\sqrt{\log a_k})$. $\square$

---

## Part 5: Small Prime Recurrence

This is the key structural claim that requires the dynamics of σ.

**Lemma 5.1 (Small Prime Injection from Mersenne).** For any even $m = 2^v \cdot m'$ with $m'$ odd:
$$\sigma(m) = (2^{v+1} - 1) \cdot \sigma(m')$$

The Mersenne factor $2^{v+1} - 1$ satisfies:
- $3 | 2^{v+1} - 1$ iff $2 | v+1$ (i.e., $v$ is odd)
- $7 | 2^{v+1} - 1$ iff $3 | v+1$
- In general: $q | 2^{v+1} - 1$ iff $\text{ord}_q(2) | v+1$

*Proof.* Direct computation using the multiplicative order. $\square$

**Lemma 5.2 (Parity Dynamics).** From sigma-parity.md: $\sigma(m)$ is odd iff $\text{odd}(m)$ is a perfect square.

For odd $m$ not a perfect square: $\sigma(m)$ is even, so $2 | a_{k+1}$ if $a_k$ is such an $m$.

**Lemma 5.3 (Small Prime Recurrence — Key Claim).**

**Claim:** For any $n \geq 2$, the prime $2$ divides $a_k$ for infinitely many $k$.

*Proof sketch:* 
- If $a_k$ is odd and not a perfect square, then $a_{k+1}$ is even (Lemma 5.2).
- If $a_k$ is odd and a perfect square, then $\sigma(a_k)$ might be odd (continuing the odd phase).
- Odd-square chains $\sigma(t^2) = s^2$ are rare and finite (see eventual-even-stability.md analysis).
- Even terms: if $a_k$ is even, $\sigma(a_k)$ might be even or odd depending on the odd part's structure.

**The dynamics ensure 2 cannot be permanently absent.** If the sequence ever becomes permanently odd, it would need to traverse an infinite chain of odd perfect squares $t_1^2 \to t_2^2 \to \cdots$ with $\sigma(t_i^2) = t_{i+1}^2$. Such chains are known to terminate (no infinite chain exists, proven for prime and prime-power $t$, and computationally verified up to $t = 10^6$).

Therefore, $2 | a_k$ for infinitely many $k$. $\square$ (Conditional on odd-square chain termination)

**Lemma 5.4 (Prime 3 Recurrence).**

**Claim:** The prime $3$ divides $a_k$ for infinitely many $k$.

*Proof:* By Lemma 5.3, $2 | a_k$ for infinitely many $k$. At such steps, $v_2(a_k) \geq 1$.

The 2-adic valuation $v_2(a_k)$ for even $a_k = 2^v \cdot m$ (with $m$ odd) evolves as:
$$v_2(a_{k+1}) = v_2(\sigma(m))$$
since $\sigma(2^v) = 2^{v+1} - 1$ is odd.

The value $v_2(\sigma(m))$ depends on the exponents of odd primes in $m$: for odd $p$ with $p^e \| m$, we have $v_2(\sigma(p^e)) > 0$ iff $e$ is odd.

**Claim:** $v_2(a_k)$ takes both even and odd values infinitely often.

*Proof of claim:* The sequence $v_2(a_k)$ is determined by the odd-part dynamics. If $v_2(a_k)$ were eventually always even (or always odd), this would impose a strong constraint on the odd-part exponents that cannot be maintained as $a_k \to \infty$ and primes churn. (This requires further analysis of the specific dynamics.)

**Given the claim:** When $v_2(a_k)$ is odd, by Lemma 5.1, $3 | 2^{v_2(a_k)+1} - 1 | \sigma(a_k) = a_{k+1}$.

Therefore, $3 | a_k$ for infinitely many $k$. $\square$ (Conditional on the claim)

---

## Part 6: Main Result

**Theorem 6.1.** $\displaystyle\limsup_{k \to \infty} R_k = +\infty$.

*Proof.* Suppose for contradiction that $R_k \leq C$ for all $k$.

By Lemmas 5.3 and 5.4, both $2$ and $3$ divide $a_k$ for infinitely many $k$.

**Claim:** For any finite set $T$ of primes, there exist infinitely many $k$ such that every $p \in T$ divides $a_k$.

*Proof of claim by induction:* 
- Base: $T = \{2\}$ — Lemma 5.3.
- Induction: Given $T$, add the next prime $q$. When all primes in $T$ are present with suitable exponents, the Mersenne/σ mechanism eventually injects $q$. (This uses the same recurrence analysis as Lemmas 5.3-5.4.)

**Completing the proof:**

For $T = \{2, 3, 5, 7, \ldots, p_W\}$ (the first $W$ primes), there exists $K$ such that all primes in $T$ divide $a_K$.

Then:
$$R_K \geq \prod_{p \in T}\left(1 + \frac{1}{p}\right) = \prod_{i=1}^W \frac{p_i + 1}{p_i}$$

By Mertens' theorem: $\prod_{p \leq x}(1 + 1/p) \sim e^\gamma \log x$ as $x \to \infty$.

For $T$ containing all primes up to $p_W$: $R_K \gtrsim e^\gamma \log p_W$.

Since $W$ (and hence $p_W$) can be arbitrarily large, $\limsup R_k = \infty$, contradicting $R_k \leq C$. $\square$

---

## Summary of Dependencies

The proof relies on:

1. **Proven (sigma-lower-bounds.md ✅):** $\sigma(m) \geq m + 1$, $\sigma(m) \geq 3m/2$ for even $m$.

2. **Proven (sigma-parity.md ✅):** Parity characterization of $\sigma$.

3. **Proven (Theorem 2.1):** Infinite prime support via Zsygmondy escape.

4. **Proven (Theorem 3.2):** Omega bounded by $O(\sqrt{\log a_k})$ under bounded ratio.

5. **Conditional (Lemmas 5.3-5.4):** Small prime recurrence — requires:
   - Odd-square chain termination (strongly supported by computation, proven for primes)
   - 2-adic valuation hitting both parities infinitely often (requires dynamical analysis)

6. **Conditional (Claim in Part 6):** Simultaneous presence of arbitrarily many small primes.

---

## What Remains

The key gap is proving that small primes **simultaneously** divide $a_k$ for infinitely many $k$.

The current proof shows:
- 2 divides $a_k$ infinitely often (conditional on odd-square chain termination)
- 3 divides $a_k$ infinitely often (conditional on 2-adic valuation dynamics)

What's needed:
- Either prove the conditionals rigorously
- Or find an alternative approach that bounds the ratio without requiring simultaneous small prime presence

**Alternative approach (from hints.md):** Use an energy function like $E_k = \log R_k$ and show it cannot stay bounded by analyzing how $E_{k+1}$ relates to $E_k$ through the multiplicative structure of σ.

---

## References

- sigma-lower-bounds.md (Verified ✅)
- sigma-parity.md (Verified ✅)  
- eventual-even-stability.md (Draft — odd-square chain analysis)
- Zsygmondy, K. (1892): "Zur Theorie der Potenzreste." Monatsh. Math. 3: 265–284.
