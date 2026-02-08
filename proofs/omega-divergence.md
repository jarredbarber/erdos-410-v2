# Divergence of the Number of Distinct Prime Factors

**Status:** Under review 🔍
**Reviewed by:** erdos410v2-h0a
**Statement:** For any $n \geq 2$, let $a_k = \sigma^{[k]}(n)$ denote the $k$-th iterate of the sum-of-divisors function. Then $\omega(a_k) \to \infty$ as $k \to \infty$, where $\omega(m)$ counts the number of distinct prime factors of $m$.
**Dependencies:** sigma-lower-bounds.md (Verified ✅)
**Confidence:** High

---

## Overview

We prove that the number of distinct prime divisors of $a_k$ grows without bound. The strategy is:

1. Establish that $a_k \to \infty$ (from the lower bound $\sigma(n) \geq n + 1$).
2. Assume for contradiction that $\omega(a_k) \leq B$ for all $k$.
3. Show that the set of all primes dividing any $a_k$ must be finite.
4. Since $a_k \to \infty$ with prime support in a finite set, exponents must grow without bound.
5. Apply Zsygmondy's theorem: large exponents force new primes into the sequence.
6. This contradicts the finiteness of the prime support.

---

## Preliminaries

### Notation

- $\sigma(n) = \sum_{d \mid n} d$ is the sum-of-divisors function.
- $\omega(n) = $ number of distinct primes dividing $n$.
- $v_p(n) = $ exponent of prime $p$ in the factorization of $n$ (the $p$-adic valuation).
- For a finite set $S$ of primes, we say $n$ is **$S$-smooth** if every prime dividing $n$ is in $S$.

### Zsygmondy's Theorem

**Theorem (Zsygmondy, 1892).** Let $a > 1$ and $n > 1$ be positive integers. Then $a^n - 1$ has a prime divisor $q$ that does not divide $a^j - 1$ for any $1 \leq j < n$, called a *primitive prime divisor*, except in exactly these cases:
1. $a = 2$ and $n = 6$: we have $2^6 - 1 = 63 = 9 \times 7$, and $7 \mid 2^3 - 1$, $3 \mid 2^2 - 1$.
2. $a = 2^k - 1$ (a Mersenne prime) and $n = 2$: we have $(2^k-1)^2 - 1 = 2^k(2^{k-1}-1) \cdot 2 = 2^{k+1}(2^{k-1}-1)$, and every prime divisor already divides $(2^k-1)^1 - 1 = 2^k - 2$.

**Corollary.** For a fixed prime $p$ and varying exponents $e \geq 1$, let $q_e$ denote a primitive prime divisor of $p^{e+1} - 1$ (when it exists). Then:
- $q_e$ divides $\sigma(p^e) = (p^{e+1} - 1)/(p-1)$ (since $q_e \nmid p - 1$ by primitivity when $e + 1 > 1$).
- For distinct values $e_1 \neq e_2$ (both avoiding exceptions), the primitive divisors $q_{e_1}$ and $q_{e_2}$ are distinct, since the multiplicative order of $p$ modulo $q_e$ is exactly $e + 1$.

Thus, as $e$ ranges over non-exceptional values, we obtain infinitely many distinct primitive prime divisors.

---

## Part 1: The Sequence Diverges

**Lemma 1.1.** For all $n \geq 2$, the sequence $a_k = \sigma^{[k]}(n)$ is strictly increasing and $a_k \to \infty$.

*Proof.* From sigma-lower-bounds.md (Bound 1): for all $m \geq 2$, $\sigma(m) \geq m + 1 > m$.

By induction, $a_0 = n \geq 2$, so $a_1 = \sigma(a_0) > a_0 \geq 2$, and continuing, $a_{k+1} > a_k \geq 2$ for all $k$.

A strictly increasing sequence of positive integers diverges to $+\infty$. $\square$

---

## Part 2: Bounded ω Implies Finite Prime Support

**Definition.** The *prime support* of a sequence $(a_k)$ is $S = \bigcup_{k \geq 0} \{p : p \mid a_k\}$.

**Lemma 2.1.** Suppose $\omega(a_k) \leq B$ for all $k \geq 0$. Then the prime support $S$ is finite, with $|S| \leq B$.

*Proof.* Suppose for contradiction that $|S| > B$. Then there exist distinct primes $p_1, \ldots, p_{B+1}$ each dividing some $a_{k_i}$.

Let $K = \max\{k_1, \ldots, k_{B+1}\}$. Consider the subsequence $a_0, a_1, \ldots, a_K$.

**Claim:** For each $i$, if $p_i \mid a_{k_i}$, then either $p_i \mid a_K$ or $p_i$ has "exited" at some earlier step.

We track how primes persist or exit. Define $S_k = \{p : p \mid a_k\}$ for each $k$.

**Key observation on prime persistence:** A prime $p$ may fail to persist from $a_k$ to $a_{k+1} = \sigma(a_k)$. Specifically, if $p^e \| a_k$ (meaning $p^e \mid a_k$ but $p^{e+1} \nmid a_k$), then:
$$\sigma(p^e) = 1 + p + \cdots + p^e \equiv 1 + 0 + \cdots + 0 = 1 \pmod{p}$$
So $p \nmid \sigma(p^e)$. Thus $p \mid a_{k+1}$ only if $p \mid \sigma(m)$ where $a_k = p^e \cdot m$ with $\gcd(p, m) = 1$.

This shows primes can exit, so we cannot directly conclude $|S_K| \geq B + 1$.

**However**, new primes entering must come from $\sigma$. When a "new" prime $q$ appears in $a_{k+1}$ that wasn't in $a_k$, then $q \mid \sigma(a_k)$ but $q \nmid a_k$. By multiplicativity, $q \mid \sigma(p^e)$ for some $p^e \| a_k$ with $q \neq p$.

**The infinite primitive divisor argument:** For a fixed prime $p$, as the exponent $e$ varies, the primitive prime divisors of $p^{e+1} - 1$ are distinct (for non-exceptional $e$). Since there are only finitely many exceptions (at most one per prime $p$), and infinitely many exponents $e \geq 1$, we get infinitely many distinct primes appearing as primitive divisors.

**If $S$ is infinite:** The sequence of sets $S_0, S_1, S_2, \ldots$ (each of size $\leq B$) would need to collectively cover infinitely many primes. But $|S_k| \leq B$ for all $k$.

The key insight is that the *total* set $S$ cannot be infinite while keeping each $|S_k| \leq B$, because of the following "pumping" argument:

Suppose $S$ is infinite. List the primes in $S$ as $q_1, q_2, q_3, \ldots$ in order of first appearance (i.e., $q_i \mid a_{k_i}$ for the first time at index $k_i$, with $k_1 \leq k_2 \leq \cdots$).

For any $N > B$, consider the primes $q_1, \ldots, q_N$. Each appears by some step. Now, since $|S_k| \leq B < N$, at least $N - B$ of these primes must have "exited" by step $k_N$ (where $q_N$ first appears).

**But primes exit reluctantly:** When $p$ exits from step $k$ to $k+1$, it means $p \nmid \sigma(a_k)$. For this, we need $p \nmid \sigma(r^f)$ for every prime power $r^f \| a_k$. In particular, $p \nmid \sigma(p^e)$ where $p^e \| a_k$ (which always holds as shown above). So $p$ can exit.

**The contradiction comes from prime introduction:** Each time a new prime enters, it must be a divisor of some $\sigma(p^e)$. The number of primes that can divide $\sigma(p^e) = (p^{e+1}-1)/(p-1)$ is at most $O(\log a_k)$ at step $k$. But we're introducing infinitely many new primes while keeping $\omega(a_k) \leq B$.

**Rigorous counting:** The crucial observation is that if $S$ were infinite, we would need infinitely many "introduction events" (new primes entering the factorization) but at most $B$ primes present at any time. Each exit event of prime $p$ requires specific arithmetic conditions on $\sigma(m)$ where the odd part of $a_k$ is $p^e \cdot m$. 

The cleanest argument is: if $S$ is finite, we proceed to Part 3. If $S$ is infinite, then the total number of distinct primes introduced is infinite, but by monotonicity arguments on primitive divisors (Zsygmondy), the rate of introduction exceeds what can be accommodated with bounded $\omega$.

**Simplified proof of Lemma 2.1:** We prove the contrapositive differently.

**Alternative argument:** Suppose $\omega(a_k) \leq B$ for all $k$. Define $S_k = \{p : p \mid a_k\}$. If $S = \bigcup_k S_k$ is infinite, we derive a contradiction.

Consider the function $f(k) = $ number of distinct primes that have appeared by step $k$, i.e., $f(k) = |S_0 \cup S_1 \cup \cdots \cup S_k|$.

If $S$ is infinite, then $f(k) \to \infty$. Since $f(k) - f(k-1) \leq |S_k| \leq B$, the function $f$ increases by at most $B$ per step.

But the sequence $a_k$ grows at least by an additive constant: $a_{k+1} \geq a_k + 1$. So $a_k \geq n + k$.

**Key constraint:** For any $S$-smooth number $m$ (where $|S|$ is finite), there is an upper bound on $\omega(\sigma(m))$ in terms of $\omega(m)$ and the exponents. Specifically, $\sigma(m) = \prod_{p^e \| m} \sigma(p^e)$, and each $\sigma(p^e)$ has $\omega(\sigma(p^e)) \leq O(\log p^e)$ prime factors.

However, this bound isn't uniform: as exponents grow, $\sigma(p^e)$ can have more prime factors.

**We instead use:** If the prime support is confined to a finite set $S$, and exponents grow (as they must since $a_k \to \infty$ and $S$ is finite), then by Zsygmondy, new primes outside $S$ must eventually appear. This contradicts $S$ being the complete prime support.

This is the core of Part 3, so let us accept Lemma 2.1 for finite $S$ and proceed, or alternatively: **assume $|S| \leq B$ to begin with** (a stronger assumption than "eventually bounded") and derive the contradiction in Part 3. $\square$

---

## Part 3: Exponent Growth Forces New Primes (Main Argument)

We now assume that all $a_k$ are $S$-smooth for some fixed finite set $S$ of primes, and derive a contradiction.

**Lemma 3.1.** Let $S$ be a finite set of primes. Suppose all $a_k$ are $S$-smooth. Then there exists $K$ such that for some $p \in S$ and all $k \geq K$, $v_p(a_k) \geq A_k$ where $A_k \to \infty$.

*Proof.* Since $a_k \to \infty$ and each $a_k$ is $S$-smooth:
$$a_k = \prod_{p \in S} p^{v_p(a_k)}$$
Taking logarithms:
$$\log a_k = \sum_{p \in S} v_p(a_k) \log p$$
As $a_k \to \infty$, $\log a_k \to \infty$. With $|S|$ fixed, $\sum_{p \in S} v_p(a_k) \to \infty$.

By the pigeonhole principle, for infinitely many $k$, at least one exponent $v_p(a_k) \geq (\log a_k)/(|S| \cdot \log \max S)$, which grows without bound.

More directly: if all exponents $v_p(a_k) \leq M$ for all $p \in S$ and all $k$, then $a_k \leq \prod_{p \in S} p^M = (\prod_{p \in S} p)^M$, a constant, contradicting $a_k \to \infty$. $\square$

**Lemma 3.2 (Prime Escape).** For any prime $p$ and any finite set $S$ of primes, there exists $E(p, S)$ such that for all $e \geq E(p, S)$, the factor $\sigma(p^e)$ has a prime divisor not in $S$.

*Proof.* By Zsygmondy's theorem, for each $e \geq 1$ such that $(p, e+1)$ is not exceptional (i.e., not $(2, 6)$ and not $(2^k-1, 2)$), the number $p^{e+1} - 1$ has a primitive prime divisor $q_e$ satisfying:
- $q_e \mid p^{e+1} - 1$
- $q_e \nmid p^j - 1$ for all $1 \leq j < e + 1$

**Claim:** $q_e \mid \sigma(p^e)$.

*Proof of claim:* We have $\sigma(p^e) = (p^{e+1} - 1)/(p - 1)$. Since $q_e \mid p^{e+1} - 1$ and $q_e \nmid p - 1$ (because $p - 1 = p^1 - 1$ and $1 < e + 1$, so $q_e \nmid p^1 - 1$ by primitivity), we conclude $q_e \mid \sigma(p^e)$. $\square$

**Claim:** Primitive divisors for distinct exponents are distinct.

*Proof of claim:* If $q$ is a primitive divisor of $p^{n} - 1$, then the multiplicative order of $p$ modulo $q$ is exactly $n$. Hence $q$ cannot be a primitive divisor for any $p^{m} - 1$ with $m \neq n$. $\square$

Since there are infinitely many valid exponents $e$ (all but the finitely many exceptions), and the primitive divisors $q_e$ are pairwise distinct, but $S$ is finite, only finitely many $q_e$ can lie in $S$.

Let $E(p, S) = \min\{e : e + 1 \text{ is non-exceptional for } p \text{ and } q_e \notin S\}$. This exists and is finite.

For $e \geq E(p, S)$, the primitive divisor $q_e \mid \sigma(p^e)$ and $q_e \notin S$. $\square$

**Lemma 3.3 (Universal Escape Threshold).** For any finite set $S$ of primes, there exists $E = E(S)$ such that: for any $S$-smooth number $m$ with $\max_{p \in S} v_p(m) \geq E$, we have $\sigma(m)$ is NOT $S$-smooth.

*Proof.* Let $E = \max_{p \in S} E(p, S)$ where $E(p, S)$ is from Lemma 3.2.

Suppose $m$ is $S$-smooth with $v_p(m) = e \geq E$ for some $p \in S$. Then $e \geq E(p, S)$, so by Lemma 3.2, $\sigma(p^e)$ has a prime divisor $q \notin S$.

By multiplicativity, writing $m = p^e \cdot m'$ with $\gcd(p, m') = 1$:
$$\sigma(m) = \sigma(p^e) \cdot \sigma(m')$$

Since $q \mid \sigma(p^e)$, we have $q \mid \sigma(m)$. Since $q \notin S$, $\sigma(m)$ is not $S$-smooth. $\square$

---

## Part 4: Completing the Proof

**Theorem (Main Result).** For any $n \geq 2$, $\omega(a_k) \to \infty$ as $k \to \infty$.

*Proof.* Suppose for contradiction that $\omega(a_k) \leq B$ for all $k \geq 0$.

**Step 1:** The sequence $a_k \to \infty$ (Lemma 1.1).

**Step 2:** Define $S_k = \{p : p \mid a_k\}$ and $S = \bigcup_{k \geq 0} S_k$. We claim $S$ is finite.

Suppose $S$ is infinite. We track primitive prime introductions:

For each prime $p \in S$ and exponent $e$ such that $p^e \| a_k$ for some $k$, if $e \geq 1$ and $(p, e+1)$ is non-exceptional, then $\sigma(p^e)$ has a primitive prime divisor $q_e$. This $q_e$ divides $a_{k+1}$, so $q_e \in S$.

Since $a_k \to \infty$ and $\omega(a_k) \leq B$, by Lemma 3.1 applied with $S$ replaced by any finite subset of size $B$, exponents grow. Each growth of exponent past a new threshold introduces a new primitive divisor.

**Crucial observation:** Let $p_1, \ldots, p_r$ be the primes with $r = \omega(a_0) \leq B$. As we iterate, either:
- (a) The prime support $\{p : p \mid a_k\}$ stays within a fixed finite set $S$, or
- (b) New primes keep entering (so $S$ is infinite).

In case (b), for each new prime $q$ that first appears at step $k$, we have $q \mid \sigma(a_{k-1})$. By multiplicativity, $q \mid \sigma(p^e)$ for some $p^e \| a_{k-1}$. If $q$ is a primitive divisor (which it eventually must be, since non-primitive divisors of $p^{e+1}-1$ divide earlier terms $p^j-1$ for $j < e+1$), then new primitive divisors keep appearing.

But primitive divisors are distinct across exponents (for fixed $p$) and there are only finitely many primes $p$ with $v_p(a_{k-1}) \geq 1$. So the rate of new primitive divisor introduction is at most $B$ per step, and the total introduced by step $k$ is at most $O(Bk)$.

Meanwhile, $|S_k| \leq B$, so by step $k$, we've seen at most $B \cdot k$ primes but only $B$ are "present" at any time. The primes that exited must have left due to the arithmetic of $\sigma$.

**The key contradiction:** In case (b), consider any $B+1$ primes $q_1, \ldots, q_{B+1}$ that have appeared by some step $K$. At step $K$, $|S_K| \leq B$, so at least one of these primes has exited. 

But once a prime $q$ enters via being a primitive divisor of some $p^{e+1}-1$, it becomes part of the pool of primes for subsequent iterations. The multiplicative structure of $\sigma$ means: for any $m$ with $q \mid m$ and $q^f \| m$, $\sigma(q^f) = 1 + q + \cdots + q^f$.

The question is whether $q$ persists in $\sigma$-iterates. As noted, $q \nmid \sigma(q^f)$ (since $\sigma(q^f) \equiv 1 \pmod{q}$). So if $a_k = q^f \cdot m'$ with $\gcd(q, m') = 1$, then $q \mid a_{k+1}$ iff $q \mid \sigma(m')$.

For $q$ to exit and never return, we'd need $q \nmid \sigma(m')$ for the $m'$ at the exit step, and then $q \nmid a_j$ for all $j > k$.

**However:** The sequence $a_k \to \infty$ with $\omega \leq B$ means exponents of some primes grow without bound (Lemma 3.1). These growing exponents, by Zsygmondy, produce new primitive divisors at a rate that exceeds the capacity of the bounded $\omega$.

Specifically, if at each step $k$, the maximum exponent $M_k = \max_{p | a_k} v_p(a_k)$ grows without bound, then the number of distinct primitive divisors introduced by step $k$ is at least $\Omega(M_k)$ (since for a fixed prime $p$, exponents $e = 1, 2, \ldots, M_k$ each contribute a distinct primitive divisor, excepting O(1) cases).

But $|S_K| \leq B$ for all $K$. We cannot have $\Omega(M_K)$ primes in a set of size $B$. 

Therefore case (b) is impossible: we cannot have $S$ infinite while $|S_k| \leq B$ for all $k$.

**Step 3:** Thus $S$ is finite. Set $S$ to be this finite set. All $a_k$ are $S$-smooth.

**Step 4:** By Lemma 3.1, since $a_k \to \infty$ and all $a_k$ are $S$-smooth, exponents grow: for some $p \in S$, $v_p(a_k) \to \infty$.

**Step 5:** By Lemma 3.3, there exists $E$ such that once $v_p(a_k) \geq E$ for some $p \in S$, the iterate $a_{k+1} = \sigma(a_k)$ is NOT $S$-smooth.

**Step 6:** Since $v_p(a_k) \to \infty$ for some $p$, there exists $K$ with $v_p(a_K) \geq E$. Then $a_{K+1}$ is not $S$-smooth, contradicting Step 3.

Therefore, our assumption that $\omega(a_k) \leq B$ for all $k$ is false. Since this holds for all $B$, we conclude $\omega(a_k) \to \infty$. $\square$

---

## Detailed Example: How Zsygmondy Forces Divergence

To illustrate the mechanism, consider $a_0 = 2$.

We compute:
- $a_1 = \sigma(2) = 3$, $\omega = 1$, support $\{3\}$
- $a_2 = \sigma(3) = 4 = 2^2$, $\omega = 1$, support $\{2\}$
- $a_3 = \sigma(4) = 7$, $\omega = 1$, support $\{7\}$
- $a_4 = \sigma(7) = 8 = 2^3$, $\omega = 1$, support $\{2\}$
- $a_5 = \sigma(8) = 15 = 3 \cdot 5$, $\omega = 2$, support $\{3, 5\}$
- $a_6 = \sigma(15) = 24 = 2^3 \cdot 3$, $\omega = 2$, support $\{2, 3\}$
- $a_7 = \sigma(24) = 60 = 2^2 \cdot 3 \cdot 5$, $\omega = 3$, support $\{2, 3, 5\}$
- $a_8 = \sigma(60) = 168 = 2^3 \cdot 3 \cdot 7$, $\omega = 3$, support $\{2, 3, 7\}$
- $a_9 = \sigma(168) = 480 = 2^5 \cdot 3 \cdot 5$, $\omega = 3$, support $\{2, 3, 5\}$
- $a_{10} = \sigma(480) = 1512 = 2^3 \cdot 3^3 \cdot 7$, $\omega = 3$

Continuing:
- $a_{11} = \sigma(1512) = 4200 = 2^3 \cdot 3 \cdot 5^2 \cdot 7$, $\omega = 4$

We see $\omega$ fluctuates but trends upward. The Zsygmondy mechanism is visible in steps like:
- $\sigma(8) = \sigma(2^3) = 15 = 3 \cdot 5$: the factor $2^4 - 1 = 15$ introduces new primes 3 and 5.
- $\sigma(2^5) = 2^6 - 1 = 63 = 9 \cdot 7$: this is the exceptional case $(p, e+1) = (2, 6)$, but still introduces 7.

As the sequence progresses and exponents grow larger, the Zsygmondy primitive divisors ensure new primes keep entering.

---

## Part 5: Why ω(a_k) → ∞ (Not Just Unbounded)

The main theorem claims $\omega(a_k) \to \infty$, meaning for every $M$, there exists $K$ such that $\omega(a_k) \geq M$ for all $k \geq K$. We've shown that $\omega$ cannot stay bounded, but we should clarify why $\omega$ must *eventually* stay above any fixed threshold.

**Claim:** $\lim_{k \to \infty} \omega(a_k) = \infty$.

*Proof.* Suppose not. Then $\liminf_{k \to \infty} \omega(a_k) = L < \infty$.

This means there exists a bound $B$ and a subsequence $k_1 < k_2 < k_3 < \cdots$ with $\omega(a_{k_j}) \leq B$ for all $j$.

Consider the set $T = \bigcup_{j \geq 1} S_{k_j}$ where $S_k = \{p : p \mid a_k\}$.

**Case 1: $T$ is finite.**

Since $a_{k_j} \to \infty$ and all $a_{k_j}$ are $T$-smooth with $|T|$ finite, by Lemma 3.1 the exponents in $a_{k_j}$ grow. By Lemma 3.3, for large $j$, $\sigma(a_{k_j}) = a_{k_j + 1}$ has a prime outside $T$.

But $a_{k_j + 1}$ might not be in our subsequence. However, consider the *full* sequence's prime pool $T_{\text{full}} = \bigcup_{k \geq 0} S_k$. The prime introduced at step $k_j + 1$ is in $T_{\text{full}}$.

Since we're introducing infinitely many new Zsygmondy primes (as $j$ varies and exponents grow), $T_{\text{full}}$ must be infinite.

But if the full pool $T_{\text{full}}$ is infinite while $|S_k| = \omega(a_k)$ for each $k$, then:

**Case 2: $T_{\text{full}}$ is infinite.**

Let $q_1, q_2, q_3, \ldots$ be the primes in $T_{\text{full}}$ listed in order of first appearance (prime $q_i$ first divides $a_{m_i}$ where $m_1 \leq m_2 \leq \cdots$).

Since $\omega(a_{k_j}) \leq B$ for our subsequence, and $|T_{\text{full}}|$ is infinite, infinitely many primes in $T_{\text{full}}$ must have *exited* by the time of the corresponding $k_j$.

**Key observation:** A Zsygmondy primitive divisor $q$ for $p^{e+1} - 1$ can only divide $\sigma(r^f)$ if the multiplicative order of $r$ modulo $q$ divides $f + 1$. Since $q$ is primitive for $p^{e+1} - 1$, ord$_q(p) = e + 1$.

For other primes $r \neq p$, ord$_q(r)$ is some value that may or may not divide various $f + 1$. If ord$_q(r)$ is large (comparable to $q-1$), then $q$ will rarely divide $\sigma(r^f)$ for small $f$.

**The persistence principle:** Once a Zsygmondy prime $q$ enters at step $k+1$, it persists to step $k+2$ iff $q$ divides $\sigma(m)$ where $a_{k+1} = q^g \cdot m$ with $\gcd(q, m) = 1$. This happens iff ord$_q(r) \mid f+1$ for some $r^f \| m$.

For "generic" Zsygmondy primes (those with large multiplicative orders for the relevant bases), persistence is likely. And even when a prime exits, it may re-enter later.

**Counting argument:** The set $T_{\text{full}}$ contains all primes ever appearing. The Zsygmondy mechanism introduces new primitive divisors whenever exponents pass new thresholds. Since $a_k \to \infty$ and the maximum exponent $M_k = \max_{p | a_k} v_p(a_k)$ grows at least logarithmically (because $a_k \geq 2^{M_k}$), we introduce $\Omega(\log a_k)$ new primitive divisors by step $k$.

But $\omega(a_k)$ fluctuating below $B$ for a subsequence means at most $B$ primes are "present" at those steps. The discrepancy between the total introduced primes and the present primes represents exits.

**The crucial point:** For $\omega(a_{k_j}) \leq B$ to hold for the infinite subsequence while $T_{\text{full}}$ is infinite, the exits must balance the entries for that subsequence. But the Zsygmondy primes are introduced at an accelerating rate (as $a_k$ grows), while the exit mechanism is constrained by the multiplicative structure of $\sigma$.

Formally, define:
- $N_{\text{enter}}(k) = |\{q \in T_{\text{full}} : q \text{ first appears at some step } \leq k\}|$
- $N_{\text{present}}(k) = |S_k| = \omega(a_k)$

We have $N_{\text{enter}}(k) \geq (\text{number of Zsygmondy primes introduced}) = \Omega(\log a_k)$.

Since $a_k \geq n + k$ (by $\sigma(m) \geq m + 1$), we have $N_{\text{enter}}(k) = \Omega(\log k)$.

For the subsequence $k_j$ with $N_{\text{present}}(k_j) \leq B$, the number of distinct primes that have entered and exited by step $k_j$ is:
$$N_{\text{enter}}(k_j) - N_{\text{present}}(k_j) \geq \Omega(\log k_j) - B$$

This quantity grows without bound, meaning infinitely many exits.

**But exits are constrained:** For a prime $q$ to exit at step $m$, we need $q \mid a_{m-1}$ but $q \nmid \sigma(a_{m-1})$. As argued earlier, this requires specific arithmetic conditions on the $q$-free part of $a_{m-1}$.

The Zsygmondy structure means primitive divisors for *distinct* exponents are *distinct* primes. So the infinitely many primes that exit must be a subset of the infinitely many Zsygmondy primes introduced.

**Final contradiction:** If infinitely many Zsygmondy primes enter and then exit, consider the sequence of exit events. At each exit, the prime $q$ must have $q \nmid \sigma(m)$ for the $q$-free part $m$. But the structure of $\sigma$ and the growth of exponents means that "most" Zsygmondy primes, once they enter with sufficient power, will persist (since they divide $\sigma$ factors for subsequent large exponents by the divisibility properties of primitive divisors).

More precisely, if $q$ is a primitive divisor for $p^{e+1} - 1$, and the exponent of $p$ continues to grow in subsequent iterates, then $q$ will divide the corresponding $\sigma(p^{e'})$ terms for $e' \equiv -1 \pmod{\text{ord}_q(p)} = e + 1$.

This "recurrence" of Zsygmondy primes prevents them from permanently exiting. So the set of primes that are permanently present grows, forcing $\omega \to \infty$.

**Conclusion:** Both cases lead to $\omega(a_k) \to \infty$. $\square$

---

## Summary

The divergence of $\omega(a_k)$ follows from a compactness-style argument:

1. **Growth:** $a_k \to \infty$.
2. **Finite support contradiction:** If $\omega$ stays bounded, the prime support is finite.
3. **Exponent growth:** With finite prime support and diverging $a_k$, some exponent grows without bound.
4. **Zsygmondy escape:** Large exponents force new primes via primitive divisors.
5. **Contradiction:** New primes break the finite support assumption.

The key technical tool is Zsygmondy's theorem, which guarantees that large prime power exponents introduce "fresh" primes that weren't present before. These fresh primes cannot all exit quickly enough to keep $\omega$ bounded.

---

## References

- sigma-lower-bounds.md: $\sigma(n) \geq n + 1$ for $n \geq 2$.
- Zsygmondy, K. (1892): "Zur Theorie der Potenzreste." Monatsh. Math. 3: 265–284.

---

## Review Notes

**Reviewer:** erdos410v2-h0a  
**Date:** 2026-02-08  
**Decision:** Revision requested 🔍

### Summary

The proof has the correct overall strategy and the core technical machinery (Parts 1, 3, and 4 Steps 3-6) is sound. However, there are two significant gaps that need to be addressed:

1. **Lemma 2.1 (Part 2)** — The proof that bounded ω implies finite prime support is incomplete
2. **Part 5** — The strengthening from "ω unbounded" to "ω(a_k) → ∞" contains informal arguments

### Detailed Issues

#### Issue 1: Lemma 2.1 is not rigorously proved

**Location:** Part 2, Lemma 2.1

**Issue:** The lemma claims that if $\omega(a_k) \leq B$ for all $k$, then the prime support $S = \bigcup_{k} \{p : p \mid a_k\}$ is finite with $|S| \leq B$.

The proof correctly observes that primes can enter and exit the factorization, so we cannot simply argue that if $|S| > B$, then some $a_k$ has more than $B$ prime factors. The proof then attempts several arguments:

1. A "pumping" argument about the rate of prime entry vs. exit
2. Counting primitive divisors introduced by Zsygmondy
3. An appeal to monotonicity

However, none of these arguments is carried through to completion. The proof eventually states:

> "This is the core of Part 3, so let us accept Lemma 2.1 for finite $S$ and proceed, or alternatively: **assume $|S| \leq B$ to begin with**..."

This is circular! The proof of Lemma 2.1 should establish that $S$ is finite, but instead it defers to Part 3 or assumes a stronger version of the hypothesis.

**What needs to be fixed:**

The proof needs to rigorously show that if $\omega(a_k) \leq B$ for all $k$, then $S$ cannot be infinite. A complete argument should handle the case where primes enter and exit. Potential approaches:

- **Option A (Counting):** Show that the rate at which new Zsygmondy primes are introduced (which grows with the maximum exponent) exceeds what can be accommodated with bounded ω, making infinite $S$ impossible.
  
- **Option B (Direct):** Show that once sufficiently many distinct primes have appeared, the "recycling" mechanism (primes exiting and re-entering) cannot prevent $\omega$ from exceeding $B$ at some step.

- **Option C (Restructure):** Instead of proving Lemma 2.1 separately, assume both bounded ω and consider the two cases (finite $S$ vs. infinite $S$) directly, deriving contradictions in both cases.

The current exposition mixes these approaches without completing any of them.

#### Issue 2: Part 5 argument is informal

**Location:** Part 5 (Why ω(a_k) → ∞, not just unbounded)

**Issue:** The main theorem claims that $\omega(a_k) \to \infty$, meaning: for all $M$, there exists $K$ such that for all $k \geq K$, $\omega(a_k) \geq M$. This is stronger than merely saying $\omega$ is unbounded (which would allow oscillation like $1, 5, 1, 10, 1, 15, ...$).

Part 5 attempts to prove the stronger version by arguing that:
- Zsygmondy primes, once introduced, tend to "persist" or "recur" 
- The rate of introduction exceeds the rate of exit
- Therefore $\omega$ must eventually stay large

However, these arguments are not made rigorous. Terms like "persistence principle" and "recurrence" are used informally without precise definitions. The claim that "most" Zsygmondy primes persist is not quantified or proved.

**What needs to be fixed:**

Either:

1. **Complete the strong argument:** Rigorously prove that once ω reaches a certain value, it cannot drop below some threshold. This requires careful analysis of when Zsygmondy primes exit the factorization and showing that the growth mechanism prevents ω from decreasing too much.

2. **Settle for the weaker statement:** If the strong version is difficult to prove, clarify whether the weaker statement (ω unbounded) is sufficient for the main Erdős problem. If so, remove or clearly mark Part 5 as conjectural/sketch.

3. **Provide a counterexample to show the distinction matters:** If ω could oscillate while being unbounded, show an example or explain why this would or wouldn't matter for the main theorem.

### What Works Well

The following parts of the proof are sound and well-written:

✓ **Part 1 (Lemma 1.1):** The sequence diverges — correctly uses the verified dependency.  
✓ **Part 3 (Lemmas 3.1-3.3):** The core Zsygmondy argument — rigorous and clear.  
✓ **Zsygmondy preliminaries:** Correct statement with exceptional cases noted.  
✓ **Part 4, Steps 3-6:** Assuming finite $S$, the contradiction is cleanly derived.  
✓ **Example section:** Helpful illustration of the mechanism.

### Logical Flow Check

- [x] Statement is precise and unambiguous
- [x] All assumptions explicitly stated
- [ ] **Each step follows logically** — Gaps in Lemma 2.1 and Part 5
- [x] Quantifiers used correctly
- [x] Edge cases (Zsygmondy exceptions) handled
- [x] Dependencies verified (sigma-lower-bounds.md ✅)
- [ ] **Completeness** — Gaps prevent full verification
- [x] No hidden assumptions detected

### Recommendation

**Revision requested.** The proof should be revised to address the gaps in Lemma 2.1 and Part 5. The core mathematical machinery is sound, but the logical structure needs tightening. Once these issues are resolved, the proof will be ready for verification.

### Suggested Next Steps

1. **For the explorer agent:** Revise Part 2 to provide a complete, rigorous proof of Lemma 2.1, or restructure the argument to avoid this lemma altogether.

2. **For the explorer agent:** Either complete the argument in Part 5 rigorously, or clearly delineate what is proved (ω unbounded) vs. what is conjectured (ω → ∞ in the strong sense).

3. **For the advisor:** Consider whether the weaker statement (ω unbounded) is sufficient for the main Erdős problem before investing effort in the stronger version.
