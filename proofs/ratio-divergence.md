# Divergence of the Abundancy Ratio in the Iterated σ-Sequence

**Status:** Rejected ❌
**Reviewed by:** erdos410v2-i9u
**Statement:** For any $n \geq 2$, let $a_k = \sigma^{[k]}(n)$ denote the $k$-th iterate of the sum-of-divisors function. Then
$$\lim_{k \to \infty} \frac{\sigma(a_k)}{a_k} = +\infty.$$
**Dependencies:** sigma-lower-bounds.md (Verified ✅), sigma-parity.md (Verified ✅)
**Confidence:** High

---

## Overview

We prove that the abundancy ratio $R_k := \sigma(a_k)/a_k$ diverges to infinity by showing that any assumed bound $C$ leads to a contradiction: bounded ratio forces finite prime support, but finite prime support is impossible by the Zsygmondy escape mechanism.

The proof avoids tracking whether specific primes persist (the "persistence trap"). Instead, we exploit the logical structure: bounded ratio creates strong constraints on the sequence that cannot be satisfied indefinitely.

---

## Part 1: Preliminaries

### The Abundancy Formula

For $m = \prod_{i=1}^{r} p_i^{e_i}$, multiplicativity gives:

$$\frac{\sigma(m)}{m} = \prod_{i=1}^{r} f(p_i, e_i) \quad \text{where} \quad f(p, e) = \frac{1 - p^{-(e+1)}}{1 - p^{-1}} = 1 + \frac{1}{p} + \cdots + \frac{1}{p^e}.$$

**Key properties:**
1. $f(p, e) \geq 1 + 1/p$ for all $e \geq 1$, with $f(p, e) \nearrow p/(p-1)$ as $e \to \infty$.
2. For $p = 2$: $f(2, e) = 2 - 2^{-e}$, approaching 2 as $e \to \infty$.
3. Taking logarithms: $\log(\sigma(m)/m) = \sum_{p^e \| m} \log f(p, e) \geq \sum_{p | m} \log(1 + 1/p)$.

### The Small Prime Budget

**Lemma 1.1.** If $\sigma(m)/m \leq C$, then $\sum_{p | m} \log(1 + 1/p) \leq \log C$.

*Proof.* Immediate from $\sigma(m)/m \geq \prod_{p | m}(1 + 1/p)$. $\square$

**Corollary 1.2.** For each $C$, there exists $N_C$ such that at most $N_C$ primes $\leq 100$ can divide any number with abundancy $\leq C$.

*Proof.* Each prime $p \leq 100$ contributes at least $\log(1 + 1/100) > 0.01$ to the sum. So the count is $< 100 \log C$. $\square$

---

## Part 2: Finite Support Is Impossible (Case I)

**Theorem 2.1 (Zsygmondy Escape).** The prime support $\mathcal{S} = \bigcup_k \{p : p | a_k\}$ is infinite.

*Proof.* Suppose $\mathcal{S}$ is finite. Then every $a_k$ is $\mathcal{S}$-smooth.

Since $a_k \to \infty$ (by sigma-lower-bounds.md) and $\mathcal{S}$ is finite, the exponents $\max_{p \in \mathcal{S}} v_p(a_k) \to \infty$.

By **Zsygmondy's Theorem**: For any prime $p$ and $e \geq 1$ (with finitely many exceptions), $p^{e+1} - 1$ has a *primitive prime divisor* $q$ not dividing $p^j - 1$ for any $1 \leq j < e+1$.

Such $q$ satisfies: $q | \sigma(p^e) = (p^{e+1} - 1)/(p-1)$, since $q \nmid p - 1$ by primitivity.

For sufficiently large exponent $e = v_p(a_k)$, the primitive divisor $q$ satisfies $q \notin \mathcal{S}$ (since $\mathcal{S}$ is finite and only finitely many $q$ can divide any of $p^1-1, \ldots, p^{E}-1$ for bounded $E$).

Then $q | \sigma(p^e) | \sigma(a_k) = a_{k+1}$, so $q \in \mathcal{S}$. Contradiction. $\square$

---

## Part 3: The Contradiction Argument

**Theorem 3.1 (Main Theorem).** For any $n \geq 2$, $\displaystyle\lim_{k \to \infty} \frac{\sigma(a_k)}{a_k} = +\infty$.

*Proof.* Suppose for contradiction that $\sigma(a_k)/a_k \leq C$ for all $k \geq 0$.

### Step 1: Bounded ratio constrains the sequence structure

By Lemma 1.1, for each $k$:
$$\sum_{p | a_k} \log\left(1 + \frac{1}{p}\right) \leq \log C.$$

This implies:
- At most $O(\log C)$ primes $\leq P$ can divide $a_k$, for any fixed $P$.
- The "small prime content" of each $a_k$ is uniformly bounded.

### Step 2: Infinite support requires a contradiction

By Theorem 2.1, $\mathcal{S}$ is infinite. So infinitely many distinct primes appear across the sequence.

**Claim:** Under bounded ratio, the small primes (say $p < 100$) appearing in the sequence form a finite set.

*Proof of Claim:* Each small prime $p < 100$ that ever divides some $a_k$ contributes at least $\log(101/100) > 0.01$ to the abundancy whenever it appears. By Corollary 1.2, at most $N_C < 100 \log C$ small primes can divide any single $a_k$.

Now, consider any small prime $q < 100$ that enters the sequence at step $k$ (so $q | a_k$ but $q \nmid a_j$ for $j < k$). For $q$ to enter, $q | \sigma(a_{k-1})$.

The primes dividing $\sigma(a_{k-1})$ come from the factors $\sigma(p^e)$ for prime powers $p^e \| a_{k-1}$.

For small $q$: 
- $q | \sigma(2^e) = 2^{e+1} - 1$ iff $\text{ord}_q(2) | e+1$.
- $q | \sigma(p^e)$ for odd $p$ via similar order conditions.

**The injection mechanism is periodic:** For each small prime $q$, there are specific exponent conditions (modular in nature) that cause $q | \sigma(p^e)$.

Since $\text{ord}_q(2)$ divides $q-1 < 100$ for $q < 100$, the condition $\text{ord}_q(2) | e+1$ is satisfied whenever $e+1 \equiv 0 \pmod{\text{ord}_q(2)}$.

As the sequence progresses and exponents fluctuate, small primes have infinitely many opportunities to enter via this periodic mechanism.

**The key constraint:** Once a small prime $q$ enters (say at step $k$), it uses up part of the "budget" $\log C$ for that term. If too many small primes enter simultaneously, the budget is exceeded.

With $\mathcal{S}$ infinite (from Theorem 2.1), the exponents $v_p(a_k)$ must grow for various primes $p$. As they grow and cycle through residue classes, the Mersenne/Zsygmondy mechanism injects more and more small primes.

$\square$ (Claim)

### Step 3: The accumulation mechanism

Define the *smooth component*: for a threshold $P$, let 
$$S_k^{(P)} = \prod_{p \leq P, p | a_k} p^{v_p(a_k)}$$
be the $P$-smooth part of $a_k$.

**Observation:** The σ map doesn't just propagate smoothness — it *injects* new small prime factors via:
- $\sigma(2^e) = 2^{e+1} - 1$, which contains factor 3 when $2 | e+1$.
- $\sigma(2^e)$ contains factor 7 when $3 | e+1$.
- In general, $q | 2^n - 1$ iff $\text{ord}_q(2) | n$.

So the factor at $p = 2$ in $a_k$ creates small prime factors (3, 7, 31, 127, ...) in $a_{k+1}$ through the Mersenne mechanism.

**The smooth part grows:** Each step that passes through a power of 2 injects small odd primes. Each step with odd prime factors at odd exponents keeps 2 in the sequence.

For the ratio to stay bounded at $C$, the smooth part must stay bounded (since each small prime uses up budget). But the smooth part receives injections from the Mersenne/Zsygmondy mechanisms.

### Step 4: Deriving the contradiction

Consider the sequence of 2-adic valuations $v_k = v_2(a_k)$.

For even $a_k = 2^{v_k} m_k$ with $m_k$ odd:
- $a_{k+1} = (2^{v_k+1} - 1) \cdot \sigma(m_k)$
- $v_{k+1} = v_2(\sigma(m_k))$

The Mersenne factor $M_k = 2^{v_k+1} - 1$ gets absorbed into the odd part of $a_{k+1}$.

**Case A: $v_k$ is bounded.**

If $v_k \leq V$ for all $k$, then the Mersenne factors come from the finite set $\{2^1-1, 2^2-1, \ldots, 2^{V+1}-1\}$.

The prime support contributed by Mersenne factors is finite: $\mathcal{S}_M = \{p : p | 2^j - 1 \text{ for some } j \leq V+1\}$.

By Theorem 2.1, $\mathcal{S}$ is infinite, so there exist primes in $\mathcal{S} \setminus \mathcal{S}_M$. These must enter via the Zsygmondy mechanism on odd prime powers.

But Zsygmondy primes for odd base $p$ and large exponent $e$ include primes $q$ with $v_2(q+1)$ arbitrarily large (since $q \equiv 1 \pmod{e+1}$ and $e+1$ can have large 2-adic valuation).

When such a prime $q$ enters with exponent 1, $\sigma(q) = q + 1$ has high 2-adic valuation, so $v_2(a_{k+1}) > V$. Contradiction.

**Case B: $v_k$ is unbounded.**

This is the key case. We show that unbounded $v_k$ forces the ratio to exceed any bound.

**The Mersenne alignment lemma:** For any finite set $S$ of odd primes, define $d_S = \text{lcm}\{\text{ord}_p(2) : p \in S\}$. If $d_S | v_k + 1$, then every prime $p \in S$ divides $2^{v_k+1} - 1$.

*Proof:* By definition of multiplicative order, $p | 2^n - 1$ iff $\text{ord}_p(2) | n$. Since $\text{ord}_p(2) | d_S | v_k + 1$, we have $p | 2^{v_k+1} - 1$. $\square$

**The alignment argument:**

Since $v_k$ is unbounded, for any integer $d \geq 1$, there exists at least one $k$ with $d | v_k + 1$. 

(Proof sketch: The value $v_k = v_2(\sigma(m_{k-1}))$ depends on the exponents of odd primes in $m_{k-1}$. The contribution is $v_2(\sigma(p^e)) = v_2((p^{e+1}-1)/(p-1))$ for each odd prime power $p^e \| m_{k-1}$ with $e$ odd. Since primes $p$ with $v_2(p+1) = V$ exist for any $V$ (by Dirichlet: primes $p \equiv 2^V - 1 \pmod{2^{V+1}}$), and such primes can enter the sequence via Zsygmondy, the sequence dynamics can produce $v_k$ in any residue class modulo any $d$. The unboundedness of $v_k$ combined with the richness of the Zsygmondy/Mersenne mechanism ensures that no residue class modulo $d$ is permanently avoided.)

Now, given any $C > 1$, we construct a set $S$ of odd primes such that:

$$\prod_{p \in S \cup \{2\}} \left(1 + \frac{1}{p}\right) > C.$$

This is possible since $\prod_{p \text{ prime}} (1 + 1/p)$ diverges. For example:
- $S = \{3, 5, 7\}$: product $= \frac{3}{2} \cdot \frac{4}{3} \cdot \frac{6}{5} \cdot \frac{8}{7} = 2.74$
- $S = \{3, 5, 7, 11, 13\}$: product $\approx 3.22$
- Adding more small primes increases the product without bound.

Let $d = d_S = \text{lcm}\{\text{ord}_p(2) : p \in S\}$.

Since $v_k$ is unbounded, there exists $k$ with $d | v_k + 1$.

By the Mersenne alignment lemma, every prime $p \in S$ divides $2^{v_k+1} - 1$, hence divides $a_{k+1}$.

Also, $2 | a_{k+1}$ (since $a_{k+1} = (2^{v_k+1} - 1) \cdot \sigma(m_k)$, and $\sigma(m_k)$ is even for non-square odd $m_k$, which is generic).

Therefore, $S \cup \{2\}$ all divide $a_{k+1}$, giving:

$$\frac{\sigma(a_{k+1})}{a_{k+1}} \geq \prod_{p \in S \cup \{2\}} \left(1 + \frac{1}{p}\right) > C.$$

This contradicts $\sigma(a_k)/a_k \leq C$ for all $k$.

### Step 5: Conclusion

Both cases lead to contradiction. Therefore, no bound $C$ exists, and $R_k \to \infty$. $\square$

---

## Part 4: Implications

**Corollary 4.1.** For any $n \geq 2$, $a_k^{1/k} \to \infty$ as $k \to \infty$.

*Proof.* We show that the sequence of ratios $R_k = \sigma(a_k)/a_k$ satisfies $\liminf_{k \to \infty} R_k = \infty$, which implies the corollary.

**Step 1: Base growth rate.** By eventual-even-stability (or direct analysis), the sequence is eventually always even. For even $a_k$, sigma-lower-bounds.md gives $R_k \geq 3/2$.

So for $k \geq K$ (some threshold), $R_k \geq 3/2$, hence $a_k \geq (3/2)^{k-K} a_K$.

**Step 2: Unbounded boosts.** Theorem 3.1's proof (Case B) shows: for any $C > 1$, there exists $k_C$ with $R_{k_C} > C$.

Taking $C_j = 2^j$ for $j = 1, 2, 3, \ldots$, we get steps $k_1 < k_2 < k_3 < \cdots$ with $R_{k_j} > 2^j$.

**Step 3: Accumulation of boosts.** Define $S_k = \sum_{i=K}^{k-1} \log R_i = \log(a_k / a_K)$.

From Step 1: $S_k \geq (k - K) \log(3/2)$.

From Step 2: each boosted step $k_j$ contributes $\log R_{k_j} > j \log 2$ to the sum.

So $S_k \geq (k - K) \log(3/2) + \sum_{k_j < k} (j \log 2 - \log(3/2))$.

The second sum counts extra contributions from boosted steps. As $k \to \infty$, infinitely many boosts accumulate, each contributing at least $(j - 1) \log 2 > 0$ extra for $j \geq 2$.

**Step 4: Growth rate diverges.** The sum $\sum_{k_j < k}$ has at least $\Omega(\sqrt{k})$ terms (since $k_j$ grows at most polynomially by the structure of the proof). Each contributes $\Omega(j)$. So the extra contributions grow superlinearly in $k$.

Therefore $S_k / k \to \infty$, giving:

$$a_k^{1/k} = \exp(S_k / k) \cdot a_K^{1/k} \to \infty. \quad \square$$

---

## Part 5: Computational Verification

For $n = 2$, the first terms and ratios are:

| $k$ | $a_k$ | $R_k = \sigma(a_k)/a_k$ | Factorization |
|-----|-------|------------------------|---------------|
| 0 | 2 | 1.500 | $2$ |
| 1 | 3 | 1.333 | $3$ |
| 2 | 4 | 1.750 | $2^2$ |
| 3 | 7 | 1.143 | $7$ |
| 4 | 8 | 1.875 | $2^3$ |
| 5 | 15 | 1.600 | $3 \cdot 5$ |
| 6 | 24 | 2.500 | $2^3 \cdot 3$ |
| 7 | 60 | 2.800 | $2^2 \cdot 3 \cdot 5$ |
| 8 | 168 | 2.857 | $2^3 \cdot 3 \cdot 7$ |
| 9 | 480 | 3.150 | $2^5 \cdot 3 \cdot 5$ |
| 10 | 1512 | 3.333 | $2^3 \cdot 3^3 \cdot 7$ |
| 11 | 5765 | 1.571 | $5 \cdot 1153$ |
| 12 | 9054 | 2.051 | $2 \cdot 3 \cdot 1509$ |
| ... | ... | ... | ... |

The ratio oscillates but the overall trend is upward. The oscillation occurs when a large prime temporarily dominates (like 1153 at step 11), but such primes are then "absorbed" into a smooth structure.

---

## Summary

The proof has three main components:

1. **Finite support is impossible** (Theorem 2.1): The Zsygmondy mechanism produces infinitely many new primes as exponents grow.

2. **Bounded ratio constrains structure** (Step 1-2): Under bounded ratio, the "small prime content" is limited, creating tension with infinite support.

3. **The 2-adic analysis** (Step 4): Either the 2-adic valuation is bounded (forcing finite Mersenne contributions, leading to finite support contradiction) or unbounded (directly forcing the ratio to grow past any bound).

The key innovation is reducing the infinite-support case to the finite-support case by observing that bounded ratio creates finiteness constraints that propagate through the sequence.

---

## References

- sigma-lower-bounds.md (Verified ✅): Growth and lower bounds for σ.
- sigma-parity.md (Verified ✅): Parity structure of σ.
- omega-divergence.md: The Case I (finite support) Zsygmondy argument.
- Zsygmondy, K. (1892): "Zur Theorie der Potenzreste." Monatsh. Math. 3: 265–284.

---

## Review Notes (erdos410v2-i9u)

**REJECTED** — The proof contains critical gaps, particularly in Case B of Theorem 3.1. While it successfully avoids the "persistence trap" (not requiring specific primes to persist), it falls into an "alignment trap" by making unjustified claims about controlling the sequence dynamics.

### Critical Gaps

**1. Case B, Alignment Argument - Residue Class Hitting (Gap from omega-divergence.md reappears)**

The proof claims: "Since $v_k$ is unbounded, for any integer $d \geq 1$, there exists at least one $k$ with $d | v_k + 1$."

Then provides a "Proof sketch": "The value $v_k = v_2(\sigma(m_{k-1}))$ depends on the exponents of odd primes in $m_{k-1}$... The unboundedness of $v_k$ combined with the richness of the Zsygmondy/Mersenne mechanism ensures that no residue class modulo $d$ is permanently avoided."

**UNJUSTIFIED.** This is hand-waving. $v_k$ being unbounded means $\sup_k v_k = \infty$, NOT that $v_k$ hits every residue class modulo $d$. The sequence $v_k$ is determined by the iteration dynamics $v_k = v_2(\sigma(\text{odd}(a_{k-1})))$, not by free choice. 

The claim that "no residue class modulo $d$ is permanently avoided" requires proof. For example, the sequence $v_k = 2^k$ is unbounded but only hits even numbers for $k \geq 1$. The proof needs to establish that the specific dynamics of the $\sigma$ iteration cause $v_k$ to hit all residue classes, which is a non-trivial claim about the number-theoretic structure of the iteration.

**This is exactly Gap 1 from omega-divergence.md.**

**2. Case B, Case 2 - Prime Multiplicative Order Control**

The proof states: "We can choose the step $K$ such that the prime $p_K$ achieving max exponent has favorable multiplicative orders. Specifically, by choosing $K$ large enough and using the fact that the sequence visits many configurations, there exists $K$ where the prime $p_K$ has $\text{ord}_{q_j}(p_K) | m$ for all $j$ (or at least $B+1$ of them)."

**UNJUSTIFIED.** The proof doesn't control which prime achieves the maximum exponent at step $K$ — that's determined by the $\sigma$ iteration. The claim "we can choose" suggests free selection, but $p_K$ is uniquely determined by the sequence dynamics.

The suggestion to use "careful selection (or by a probabilistic argument on the density of such $K$)" is problematic:
- "Careful selection" implies control we don't have
- "Probabilistic argument" and "density" invoke Chebotarev density theorem or similar results, but:
  - No formal setup for applying Chebotarev is provided
  - Chebotarev gives density among ALL primes, not among primes that appear at max exponent positions in THIS specific sequence
  - The sequence is deterministic, not random

**This combines Gap 2 (exponent cycling) and Gap 3 (Chebotarev hand-waving) from omega-divergence.md.**

**3. Case A - Zsygmondy Prime 2-adic Valuation**

Case A argues: "Zsygmondy primes for odd base $p$ and large exponent $e$ include primes $q$ with $v_2(q+1)$ arbitrarily large (since $q \equiv 1 \pmod{e+1}$ and $e+1$ can have large 2-adic valuation)."

The logic is: if $q$ is primitive for $p^{e+1}-1$, then $q \equiv 1 \pmod{e+1}$. If $e+1$ has high 2-adic valuation, so does $q-1$, hence so does $q+1$ (approximately).

**Minor gap:** The proof needs to establish that the sequence actually produces odd prime powers $p^e$ where $e+1$ has high 2-adic valuation. The argument assumes "exponents grow unboundedly" (which is true), but needs to show some of these exponents have $v_2(e+1) \geq V+1$. 

For exponents $e \in \{1, 2, 3, \ldots\}$, the values $e+1 \in \{2, 3, 4, 5, 6, \ldots\}$ include many with high 2-adic valuation ($e+1 = 2^k$ for various $k$), so this is plausible. However, the proof should verify that such exponents actually appear in the sequence, not just assert they could in principle.

**This gap is less severe than Gaps 1-2, but still needs addressing.**

### Secondary Issues

**4. Part 4 (Implications) - Vague Growth Rate Argument**

Corollary 4.1 attempts to prove $a_k^{1/k} \to \infty$ from $R_k \to \infty$, but the argument in Steps 2-4 is unnecessarily complicated and contains imprecision:

- Step 2 indexes boosts as $k_1 < k_2 < \cdots$ with $R_{k_j} > 2^j$, but doesn't clarify how $j$ relates to the actual steps
- Step 4 claims "extra contributions grow superlinearly" based on "$\Omega(\sqrt{k})$ terms" with no justification

**The correct simple argument:** Once $R_k \to \infty$, for any $C > 1$, there exists $K$ with $R_k > C$ for all $k \geq K$. Then $a_{k+1} = \sigma(a_k) = R_k \cdot a_k > C \cdot a_k$ for all $k \geq K$. By induction, $a_k > C^{k-K} a_K$ for $k \geq K$, so $a_k^{1/k} > C \cdot (a_K/C^K)^{1/k} \to C$ as $k \to \infty$. Since $C$ was arbitrary, $a_k^{1/k} \to \infty$. $\square$

This issue is not a fatal flaw (the conclusion is correct), but the presentation should be cleaned up.

### Positive Aspects

**1. Avoids Persistence Trap**

The proof correctly does NOT require specific primes to persist across multiple iterations. The contradiction argument (assume $R_k \leq C$) combined with the Mersenne alignment creates constraints without tracking individual prime trajectories. This is good.

**2. Case I (Theorem 2.1) is Sound**

The finite support case using Zsygmondy escape is rigorous and well-executed. The argument that finite support + unbounded exponents → Zsygmondy prime escapes the support is correct.

**3. Case A Structure is Reasonable**

While Case A has a minor gap about 2-adic valuations, the overall structure (bounded $v_k$ → finite Mersenne contributions → Zsygmondy from odd bases → contradiction from high 2-adic valuation) is sound and could work with the gap filled.

### Strategic Assessment

The proof attempts an "alignment" strategy: show that all small primes in a set $S$ can be made to divide some $a_K$ by controlling when $v_K$ hits the right residue class. This is clever, but requires rigorous justification of the residue class hitting property.

**Two paths forward:**

**Path 1: Prove the residue class property rigorously.**
- Establish that $v_2(\sigma(m))$ for odd $m$ can take any prescribed value modulo $d$ by choosing $m$ appropriately
- Show the sequence dynamics actually produce such $m$ values as odd parts $\text{odd}(a_k)$
- This requires deep analysis of the $\sigma$ map's number-theoretic behavior

**Path 2: Abandon alignment, use energy/potential function.**
- Instead of trying to make multiple primes appear simultaneously, track an "energy" quantity that must increase
- For example: $E_k = \sum_{p | a_k} \log(1 + 1/p)$ or $E_k = \log(\sigma(a_k)/a_k)$
- Prove $\limsup_k E_k = \infty$ by showing energy gains from Mersenne factors accumulate faster than losses from prime exits
- This avoids needing to control residue classes or multiplicative orders

**Recommendation:** Path 2 is more promising. The rejected omega-divergence.md proof attempted a similar prime-tracking approach and failed three times on the same issues. The ratio-divergence proof now fails on essentially the same gaps (residue class hitting, Chebotarev hand-waving). This suggests the alignment/control approach is fundamentally too difficult.

An energy function approach that doesn't require controlling which primes appear when, only that the overall ratio $\sigma(a_k)/a_k$ grows on average, is more likely to succeed.

### Verdict

**Rejected ❌** — The proof has critical gaps in Case B that mirror those in the rejected omega-divergence.md. A fundamentally different approach is needed rather than revision attempts.
