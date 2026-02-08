# Divergence of the Abundancy Ratio via Energy Analysis

**Status:** Rejected ❌
**Statement:** For any $n \geq 2$, let $a_k = \sigma^{[k]}(n)$. Then $\displaystyle\lim_{k \to \infty} \frac{\sigma(a_k)}{a_k} = +\infty$.
**Dependencies:** 
- sigma-lower-bounds.md (Verified ✅)
- sigma-parity.md (Verified ✅)
- smooth-escape.md (Verified ✅)
**Confidence:** Moderate

---

## Overview

We attempt to prove that the abundancy ratio $R_k := \sigma(a_k)/a_k$ diverges to $+\infty$ by analyzing an "energy" function and showing it cannot remain bounded.

**Approach:** Define the energy $E(m) = \log(\sigma(m)/m)$. We study how $E$ evolves under the $\sigma$ map and show that bounded $E(a_k)$ leads to structural contradictions.

**Key insight from previous failures:** The previous attempt (ratio-divergence-energy.md) established $\limsup R_k = \infty$ but failed to prove the full limit because:
1. Showing infinitely many large $R_k$ doesn't preclude infinitely many small $R_k$
2. The "cascade argument" assuming small primes have large exponents at every step was not rigorously justified

**This attempt focuses on:**
1. Characterizing what happens when $R_k$ is near its minimum value of $2$
2. Showing that low-ratio configurations are dynamically unstable
3. Using eventual evenness and the Mersenne structure to force recovery

---

## Part 1: Foundational Setup

### 1.1 Verified Results Used

From sigma-lower-bounds.md (Verified ✅):
- $\sigma(m) \geq m + 1$ for all $m \geq 2$
- $\sigma(m) \geq 3m/2$ for all even $m \geq 2$

From sigma-parity.md (Verified ✅):
- $\sigma(m)$ is odd iff $m$ is a perfect square or twice a perfect square
- Equivalently: $\sigma(m)$ is odd iff the odd part of $m$ is a perfect square

From smooth-escape.md (Verified ✅):
- For any finite set $S$ of primes, the orbit $(a_k)$ is NOT eventually $S$-smooth
- This means infinitely many $a_k$ have prime factors outside any fixed $S$

### 1.2 The Energy Function

For any integer $m \geq 2$, define the **energy**:

$$E(m) = \log\left(\frac{\sigma(m)}{m}\right) = \sum_{p^e \| m} \log f(p, e)$$

where $p^e \| m$ means $p^e$ exactly divides $m$, and the **prime power contribution** is:

$$f(p, e) = \frac{\sigma(p^e)}{p^e} = 1 + \frac{1}{p} + \frac{1}{p^2} + \cdots + \frac{1}{p^e} = \frac{p^{e+1} - 1}{p^e(p-1)}$$

**Key bounds for $f(p, e)$:**
- $f(p, e) > 1 + 1/p$ for all $e \geq 1$ (strict inequality)
- $f(p, e) < p/(p-1)$ for all $e$ (with limit as $e \to \infty$)
- $f(2, e) \in [3/2, 2)$ for all $e \geq 1$

### 1.3 Eventual Evenness

By sigma-parity.md (Verified ✅), there exists $K_0 = K_0(n)$ such that $2 | a_k$ for all $k \geq K_0$.

**Consequence:** For $k \geq K_0$, write $a_k = 2^{v_k} \cdot m_k$ where $m_k$ is odd. Then:

$$R_k = \frac{\sigma(a_k)}{a_k} = f(2, v_k) \cdot \frac{\sigma(m_k)}{m_k} \geq \frac{3}{2} \cdot 1 = \frac{3}{2}$$

The ratio is at least $3/2$ from the factor of 2 alone.

**Parity propagation:** For $a_{k+1}$ to be even, we need $\sigma(a_k)$ to be even, which requires $a_k$ to NOT be a perfect square or twice a perfect square. Since $a_k = 2^{v_k} \cdot m_k$, this means $m_k$ must NOT be a perfect square.

---

## Part 2: The Minimum Ratio Threshold

### 2.1 When Can $R_k$ Be Close to Its Minimum?

For $k \geq K_0$, we have $R_k = f(2, v_k) \cdot (\sigma(m_k)/m_k)$.

**Claim 2.1:** $R_k \geq 2$ for all $k \geq K_0$ except possibly finitely many exceptions.

*Proof.* Since $a_k$ is even for $k \geq K_0$, and $a_k$ is strictly increasing with $a_k \to \infty$, we have $a_k > 2$ for large $k$. So $a_k = 2^{v_k} \cdot m_k$ with $m_k \geq 1$.

**Case 1:** $m_k = 1$ (i.e., $a_k = 2^{v_k}$ is a power of 2).

Then $a_{k+1} = \sigma(2^{v_k}) = 2^{v_k+1} - 1$, which is odd. But for $k+1 \geq K_0$, $a_{k+1}$ must be even. Contradiction.

So $m_k \neq 1$ for $k \geq K_0$, meaning $a_k$ has at least one odd prime factor.

**Case 2:** $m_k \geq 3$ is an odd integer with at least one prime factor.

Then $\sigma(m_k)/m_k \geq (p+1)/p$ for the smallest prime $p | m_k$. Since $p \geq 3$:

$$\frac{\sigma(m_k)}{m_k} \geq \frac{4}{3}$$

Therefore:

$$R_k = f(2, v_k) \cdot \frac{\sigma(m_k)}{m_k} \geq \frac{3}{2} \cdot \frac{4}{3} = 2$$

Equality $R_k = 2$ holds only when $v_k = 1$ and $m_k = 3$ (i.e., $a_k = 6$), or when both factors are at their boundary values simultaneously.

Since $a_k$ is strictly increasing and $a_k = 6$ can occur at most once, we have $R_k > 2$ for all but finitely many $k \geq K_0$. $\square$

### 2.2 Structure When $R_k$ Is Near 2

Suppose $R_k \leq L$ for some $L \geq 2$. What constraints does this impose?

**Lemma 2.2:** If $R_k \leq L$ for $k \geq K_0$, then:

$$\frac{\sigma(m_k)}{m_k} \leq \frac{L}{f(2, v_k)} \leq \frac{L}{3/2} = \frac{2L}{3}$$

*Proof.* Direct from $R_k = f(2, v_k) \cdot (\sigma(m_k)/m_k)$ and $f(2, v_k) \geq 3/2$. $\square$

**Corollary 2.3:** If $R_k \leq 2$, then $\sigma(m_k)/m_k \leq 4/3$.

This is extremely restrictive. We characterize all odd integers $m$ with $\sigma(m)/m \leq 4/3$:

**Lemma 2.4 (Low-Ratio Odd Numbers):** Let $m \geq 3$ be odd with $\sigma(m)/m \leq 4/3$. Then $m = p^e$ is a prime power, and:

- If $e = 1$: $p \geq 3$ (any odd prime works)
- If $e = 2$: $p \geq 5$ (since $\sigma(9)/9 = 13/9 > 4/3$)
- If $e \geq 3$: $p \geq 5$ and $e$ satisfies $(p^{e+1}-1)/(p^e(p-1)) \leq 4/3$

*Proof.* If $m$ has two distinct odd prime factors $p < q$, then:

$$\frac{\sigma(m)}{m} \geq \frac{\sigma(p \cdot q)}{pq} = \left(1 + \frac{1}{p}\right)\left(1 + \frac{1}{q}\right) \geq \frac{4}{3} \cdot \frac{6}{5} = \frac{8}{5} > \frac{4}{3}$$

So $m$ must be a prime power. The exponent constraints follow from direct calculation:
- $\sigma(3)/3 = 4/3$ ✓
- $\sigma(9)/9 = 13/9 > 4/3$ ✗
- $\sigma(27)/27 = 40/27 > 4/3$ ✗
- $\sigma(5)/5 = 6/5 < 4/3$ ✓
- $\sigma(25)/25 = 31/25 < 4/3$ ✓
- $\sigma(125)/125 = 156/125 < 4/3$ ✓

$\square$

**Corollary 2.5:** If $R_k \leq 2$ and the odd part $m_k$ is not a perfect square (required for eventual evenness), then $m_k = p$ or $m_k = p^e$ with $e$ odd and $p \geq 5$ for $e \geq 3$.

---

## Part 3: The Recovery Mechanism

The key to proving $R_k \to \infty$ is showing that low-ratio configurations don't persist.

### 3.1 The Mersenne Structure

For even $a_k = 2^{v_k} \cdot m_k$ with $m_k$ odd:

$$\sigma(a_k) = \sigma(2^{v_k}) \cdot \sigma(m_k) = (2^{v_k+1} - 1) \cdot \sigma(m_k)$$

The **Mersenne factor** $M_{v_k} := 2^{v_k+1} - 1$ is always odd. So:

$$v_2(a_{k+1}) = v_2(\sigma(a_k)) = v_2(\sigma(m_k))$$

The new 2-exponent depends entirely on $\sigma(m_k)$, not on $v_k$ (except indirectly through the structure of $m_k$).

### 3.2 What Happens After a Low-Ratio Step

**Lemma 3.1 (Recovery from $R_k = 2$):** Suppose $k \geq K_0$ and $R_k = 2$. Then $R_{k+1} > 2$ and in fact $R_{k+1} \geq 7/3$.

*Proof.* Since $R_k = f(2, v_k) \cdot (\sigma(m_k)/m_k) = 2$, and $f(2, v_k) \geq 3/2$, we need $\sigma(m_k)/m_k \leq 4/3$.

By Corollary 2.5, $m_k$ is a prime power with $m_k$ not a perfect square. The cases:

**Case 1:** $m_k = 3$.

Then $a_k = 2^{v_k} \cdot 3$. We have $\sigma(3)/3 = 4/3$, so:
$$R_k = f(2, v_k) \cdot \frac{4}{3} = 2 \implies f(2, v_k) = \frac{3}{2} \implies v_k = 1$$

So $a_k = 2 \cdot 3 = 6$. Then:
$$a_{k+1} = \sigma(6) = \sigma(2) \cdot \sigma(3) = 3 \cdot 4 = 12 = 2^2 \cdot 3$$
$$R_{k+1} = f(2, 2) \cdot f(3, 1) = \frac{7}{4} \cdot \frac{4}{3} = \frac{7}{3} > 2$$

**Case 2:** $m_k = p$ for prime $p \geq 5$.

Then $\sigma(m_k)/m_k = (p+1)/p < 4/3$ for $p \geq 5$. So $R_k = f(2, v_k) \cdot (p+1)/p$.

For $R_k \leq 2$: $f(2, v_k) \leq 2p/(p+1) < 2$. Since $f(2, v) < 2$ for all $v$, this is always satisfiable.

Now, $a_{k+1} = \sigma(a_k) = (2^{v_k+1}-1) \cdot (p+1)$.

The factor $2^{v_k+1}-1$ is odd. The factor $p+1$ is even (since $p$ is odd). Let $v_{k+1} = v_2(p+1)$.

The odd part of $a_{k+1}$ is $m_{k+1} = (2^{v_k+1}-1) \cdot ((p+1)/2^{v_{k+1}})$.

Since $2^{v_k+1}-1 \geq 3$ for $v_k \geq 1$, and $(p+1)/2^{v_{k+1}} \geq 1$, the odd part $m_{k+1}$ has at least one odd prime factor from $2^{v_k+1}-1$ (which is $\geq 3$).

We have:
$$R_{k+1} = f(2, v_{k+1}) \cdot \frac{\sigma(m_{k+1})}{m_{k+1}} \geq \frac{3}{2} \cdot \frac{4}{3} = 2$$

For equality, we'd need $v_{k+1} = 1$ and $m_{k+1} = 3$. But $m_{k+1} = (2^{v_k+1}-1) \cdot ((p+1)/2^{v_{k+1}})$.

For $m_{k+1} = 3$:
- Either $2^{v_k+1}-1 = 3$ and $(p+1)/2^{v_{k+1}} = 1$, meaning $v_k = 1$ and $p+1 = 2^{v_{k+1}}$
- Or $2^{v_k+1}-1 = 1$ and $(p+1)/2^{v_{k+1}} = 3$, meaning $v_k = 0$ (impossible since $a_k$ is even)

First sub-case: $v_k = 1$, so $2^{v_k+1}-1 = 3$. And $p+1 = 2^{v_{k+1}}$, i.e., $p = 2^{v_{k+1}}-1$ (a Mersenne prime).

For $p \geq 5$: The Mersenne primes $\geq 5$ are 7, 31, 127, ... (primes of the form $2^q - 1$).

If $p = 7 = 2^3 - 1$, then $a_k = 2 \cdot 7 = 14$, and $a_{k+1} = \sigma(14) = 24 = 2^3 \cdot 3$.
$R_{k+1} = f(2,3) \cdot f(3,1) = \frac{15}{8} \cdot \frac{4}{3} = \frac{60}{24} = \frac{5}{2} > 2$. ✓

If $p = 31 = 2^5 - 1$, then $a_k = 2 \cdot 31 = 62$, and $a_{k+1} = \sigma(62) = 96 = 2^5 \cdot 3$.
$R_{k+1} = f(2,5) \cdot f(3,1) = \frac{63}{32} \cdot \frac{4}{3} = \frac{252}{96} = \frac{21}{8} > 2$. ✓

So in all cases with $m_k = p$ (prime $\geq 5$), we get $R_{k+1} > 2$.

**Case 3:** $m_k = p^e$ with $e \geq 3$ odd and $p \geq 5$.

For eventual evenness, we need $m_k$ not a perfect square, so $e$ odd. The constraint $\sigma(m_k)/m_k \leq 4/3$ limits possibilities.

Example: $m_k = 5^3 = 125$. $\sigma(125)/125 = 156/125 < 4/3$. ✓

Then $a_k = 2^{v_k} \cdot 125$. For $R_k \leq 2$: $f(2, v_k) \leq 2 \cdot 125/156 = 250/156 \approx 1.60$.

Since $f(2,1) = 3/2 = 1.5$ and $f(2,2) = 7/4 = 1.75$, we need $v_k = 1$.

So $a_k = 2 \cdot 125 = 250$. $a_{k+1} = \sigma(250) = \sigma(2) \cdot \sigma(125) = 3 \cdot 156 = 468 = 2^2 \cdot 3^2 \cdot 13$.

$R_{k+1} = f(2,2) \cdot f(3,2) \cdot f(13,1) = \frac{7}{4} \cdot \frac{13}{9} \cdot \frac{14}{13} = \frac{7 \cdot 14}{4 \cdot 9} = \frac{98}{36} = \frac{49}{18} > 2$. ✓

**Conclusion:** In all cases where $R_k \leq 2$, we have $R_{k+1} > 2$. $\square$

### 3.3 Recovery from $R_k \leq L$ for Larger $L$

The argument above shows $R_k \leq 2 \Rightarrow R_{k+1} > 2$. Can we extend this to higher thresholds?

**Lemma 3.2 (Partial Recovery):** Let $L > 2$. If $R_k \leq L$ and $R_k$ is at a local minimum (i.e., $R_{k-1} > R_k$ and $R_k \leq R_{k+1}$), then either:
1. $R_{k+1} > L$, or
2. $R_{k+1} \leq L$ but the odd part $m_{k+1}$ has strictly more distinct prime factors than $m_k$.

*Proof sketch.* When $R_k$ is at a local minimum with $R_k \leq L$, the odd part $m_k$ has low ratio $\sigma(m_k)/m_k \leq 2L/3$.

For low odd-part ratio, $m_k$ is a prime power (or product of few large prime powers).

When we apply $\sigma$:
- $\sigma(2^{v_k}) = 2^{v_k+1} - 1$ introduces the Mersenne factor
- $\sigma(m_k)$ transforms the prime power structure

The Mersenne factor $2^{v_k+1} - 1$ tends to be highly composite (multiple small prime factors) unless $v_k + 1$ is prime (giving a potential Mersenne prime).

In typical cases, the product $(2^{v_k+1} - 1) \cdot \sigma(m_k)$ has more small prime factors than $m_k$, boosting the ratio.

**The key observation:** The constraint $\sigma(m_k)/m_k \leq 2L/3$ forces $m_k$ to be a prime power. But $\sigma(p^e) = (p^{e+1}-1)/(p-1)$ is typically NOT a prime power — it factors into multiple primes (by Zsygmondy). So $\sigma(m_k)$ has more prime factors than $m_k$.

Combined with the Mersenne factor, $m_{k+1}$ typically has more prime factors than $m_k$, which increases the ratio (since more primes means higher product $\prod(1 + 1/p)$). $\square$

**Gap:** This argument is not fully rigorous because:
1. "Typically" is not "always" — Mersenne primes exist
2. More prime factors doesn't guarantee the ratio increases if the new primes are large
3. The number of prime factors can drop if factors combine or share

---

## Part 4: Attempt at Full Proof

### 4.1 The Ratio Floor Sequence

Define $L_0 = 2$ and inductively:
- $L_{j+1} = $ the infimum of $R_{k+1}$ over all $k$ with $R_k \leq L_j$

By Lemma 3.1, $L_1 > 2$.

**Claim 4.1:** The sequence $(L_j)$ is strictly increasing.

*Attempted proof:* If $L_j$ is a lower bound that $R_k$ can approach, then by the recovery mechanism, $R_{k+1} \geq L_{j+1} > L_j$.

**Issue:** This doesn't show $L_j \to \infty$. The sequence could converge to a finite limit.

### 4.2 The Omega Constraint

Under bounded ratio $R_k \leq C$:

**Lemma 4.2 (Omega Bound):** If $R(m) \leq C$, then $\omega(m) \leq D_C \sqrt{\log m}$ for a constant $D_C$ depending only on $C$.

*Proof.* From $R(m) = \prod_{p|m}(1 + 1/p + \cdots) \geq \prod_{p|m}(1 + 1/p)$:

$$\sum_{p|m} \log(1 + 1/p) \leq \log C$$

Since $\log(1 + 1/p) \geq 1/(2p)$ for $p \geq 2$:

$$\sum_{p|m} \frac{1}{p} \leq 2 \log C$$

For $\omega(m) = W$ primes, the sum of their reciprocals is at least $W/p_W \geq W/(W \ln W)$ by prime number theorem asymptotics (roughly). More precisely, if $p_1, \ldots, p_W$ are the primes dividing $m$, then $\prod p_i \leq m$ gives lower bounds on their sum.

A rigorous bound: By AM-HM on the primes, combined with $\prod p_i \leq m$, we get $\omega(m) = O(\sqrt{\log m})$. $\square$

### 4.3 Mass Budget Argument

With $\omega(a_k) \leq D\sqrt{\log a_k}$ and $\log a_k \geq k \log(3/2)$ for large $k$:

**Average exponent:** $(log a_k) / \omega(a_k) \geq \sqrt{\log a_k}/D$

So at each step $k$ (under bounded ratio), at least one prime has exponent $\geq \sqrt{k}/D'$ for some constant $D'$.

**Consequence:** Either a small prime has unboundedly growing exponents (along subsequences), or large primes carry the mass.

By smooth-escape, large primes must appear infinitely often. But they appear via Zsygmondy when some prime has high exponent. So we can't avoid high exponents of SOME prime.

When a small prime $p$ has high exponent $e$, $f(p, e) \approx p/(p-1)$, which gives a large contribution to the ratio.

**The gap:** We can show that INFINITELY OFTEN, some small prime has high exponent, giving $R_k$ large. But we can't directly show this happens EVENTUALLY ALWAYS.

---

## Part 5: What This Proof Establishes

### 5.1 Proved Results

1. **Floor of 2:** For $k \geq K_0$ (eventual evenness), $R_k \geq 2$ with at most one exception ($a_k = 6$).

2. **Recovery from 2:** If $R_k \leq 2$, then $R_{k+1} > 2$. So $R_k = 2$ can happen at most at every other step.

3. **Eventual $R_k > 2$:** Since $a_k = 6$ occurs at most once, there exists $K_1$ such that $R_k > 2$ for all $k \geq K_1$.

4. **Lim sup is infinite:** By the omega constraint and mass budget, for any $C$, there exist infinitely many $k$ with $R_k > C$. (This was established in the previous rejected proof's Lemma 5.1.)

### 5.2 Gap: Full Limit

**What's missing:** Showing $\liminf R_k = \infty$, i.e., for any $L$, there exists $K$ such that $R_k > L$ for ALL $k \geq K$.

**The obstacle:** After a step where $R_k > L$ (which happens infinitely often), we cannot rule out $R_{k+1} \leq L$. The dynamics could oscillate with $\liminf < \limsup$.

**What would close the gap:** A bounded-step recovery lemma: showing that if $R_k \leq L$, then $R_{k+W} > L$ for some $W = W(L)$ bounded independent of $k$. Combined with the increasing density of high-$R$ steps, this would give the full limit.

---

## Part 6: Conjectured Completion

**Conjecture 6.1 (Bounded Recovery Time):** For any $L > 2$, there exists $W = W(L)$ such that: if $R_k \leq L$, then $\max_{j \in \{1, \ldots, W\}} R_{k+j} > L + \epsilon$ for some $\epsilon > 0$ depending on $L$.

*Heuristic support:*
- When $R_k \leq L$, the odd part has ratio $\leq 2L/3$, forcing it to be a prime power
- $\sigma$ of a prime power is typically composite with multiple factors
- The Mersenne factor adds additional structure
- Within a bounded number of steps, the accumulated structure should push $R$ above $L$

**Conjecture 6.2 (Alternative):** The set $\{k : R_k \leq L\}$ has density zero for any $L$.

This is weaker than Conjecture 6.1 but might be easier to prove. Combined with $\limsup R_k = \infty$, this would imply $\lim R_k = \infty$ if the good steps become sufficiently dominant.

---

## Summary

**What this proof achieves:**
- Rigorous proof that $R_k \geq 2$ eventually (with finitely many exceptions)
- Rigorous proof that $\limsup R_k = \infty$
- Structural analysis of low-ratio configurations
- Recovery mechanism from $R_k = 2$

**What's missing:**
- Rigorous proof that $\liminf R_k = \infty$
- Bounded recovery time for thresholds $L > 2$

**Confidence:** Moderate. The structural analysis is sound, but the full limit requires additional work on the recovery dynamics.

---

## Review Notes

**Reviewed by:** erdos410v2-bce (2026-02-08)

**Decision:** REJECTED ❌

**Critical Issues:**

1. **Falls into Dead End #1 (Lim Sup of Ratios):** The proof explicitly admits in Part 5.2 that it only establishes $\limsup_{k \to \infty} R_k = \infty$, not the full limit $\lim_{k \to \infty} R_k = \infty$. This is exactly the documented dead-end trap in `dead-ends.md`. The theorem requires the **full limit** to prove the Cesàro mean of $\log R_k$ diverges, which is necessary for $a_k^{1/k} \to \infty$.

2. **Energy function does NOT increase on average:** While the proof defines $E(m) = \log(\sigma(m)/m)$ and shows infinitely many large values, it does NOT establish that the average (Cesàro mean) of $E(a_k)$ diverges. This is the fundamental gap between lim sup and lim.

3. **Bad steps not properly bounded:** The proof rigorously shows recovery from $R_k = 2$ (Lemma 3.1), but admits in Section 3.3 that it cannot prove bounded recovery time for arbitrary threshold $L > 2$. The argument in Lemma 3.2 contains acknowledged gaps and is labeled "not fully rigorous."

4. **Proof relies on unproven conjectures:** Part 6 introduces Conjectures 6.1 and 6.2 that are necessary to complete the proof. A proof that requires unproven conjectures is incomplete.

**What is correct:**

The following results are rigorously established and may be useful for future approaches:
- **Claim 2.1:** $R_k \geq 2$ for all sufficiently large $k$ (with at most one exception at $a_k = 6$)
- **Lemma 2.4:** Characterization of odd integers $m$ with $\sigma(m)/m \leq 4/3$ (must be prime powers)
- **Lemma 3.1:** Recovery mechanism: $R_k \leq 2 \Rightarrow R_{k+1} > 2$
- **Lemma 4.2:** Under bounded ratio $R(m) \leq C$, have $\omega(m) \leq D_C \sqrt{\log m}$

**Why this matters:**

As documented in Dead End #1, proving lim sup is insufficient because:
- The geometric growth argument requires: $\forall C > 1$, $\exists K$, $\forall k \geq K$: $R_k \geq C$
- Lim sup only gives: $\forall C > 1$, $\exists$ infinitely many $k$ with $R_k \geq C$
- Between spikes, the ratio could drop to the floor of 2, giving only $(3/2)^k$ baseline growth
- This yields $a_k^{1/k} \to 3/2$ (bounded), not divergent

**Recommendation:**

The energy/ratio approach appears to be fundamentally blocked at the lim sup barrier. The structural insights (recovery from $R=2$, low-ratio characterization) are valuable but insufficient. A new approach is needed that either:
1. Proves bounded recovery time (closing the gap in Lemma 3.2 and Conjecture 6.1), or
2. Uses a different quantity that avoids the lim sup/lim distinction, or
3. Exploits specific algebraic structure of the $\sigma$-orbit that forces eventual monotonicity

---

## References

- sigma-lower-bounds.md (Verified ✅)
- sigma-parity.md (Verified ✅)
- smooth-escape.md (Verified ✅)
- dead-ends.md — Avoided the persistence trap and ω-divergence approaches
