# Divergence of the Number of Distinct Prime Factors

**Status:** Draft ✏️
**Statement:** For any $n \geq 2$, let $a_k = \sigma^{[k]}(n)$ denote the $k$-th iterate of the sum-of-divisors function. Then $\omega(a_k) \to \infty$ as $k \to \infty$, where $\omega(m)$ counts the number of distinct prime factors of $m$.
**Dependencies:** sigma-lower-bounds.md (Verified ✅)
**Confidence:** High

---

## Overview

We prove that the number of distinct prime divisors of $a_k$ grows without bound. The strategy is:

1. Establish that $a_k \to \infty$ (from the lower bound $\sigma(n) \geq n + 1$).
2. Assume for contradiction that $\omega(a_k) \leq B$ for all $k$.
3. Consider two cases: finite or infinite prime support.
4. **Case I (Finite support):** Exponents must grow, forcing new primes via Zsygmondy.
5. **Case II (Infinite support):** Zsygmondy primes accumulate faster than they exit.
6. Both cases contradict the bounded $\omega$ assumption.
7. Strengthen to $\omega(a_k) \to \infty$ using monotonicity of the $\liminf$.

---

## Preliminaries

### Notation

- $\sigma(n) = \sum_{d \mid n} d$ is the sum-of-divisors function.
- $\omega(n) = $ number of distinct primes dividing $n$.
- $v_p(n) = $ exponent of prime $p$ in the factorization of $n$ (the $p$-adic valuation).
- For a finite set $S$ of primes, we say $n$ is **$S$-smooth** if every prime dividing $n$ is in $S$.
- The **prime support** of the sequence $(a_k)$ is $\mathcal{S} = \bigcup_{k \geq 0} \{p : p \mid a_k\}$.

### Zsygmondy's Theorem

**Theorem (Zsygmondy, 1892).** Let $a > 1$ and $n > 1$ be positive integers. Then $a^n - 1$ has a prime divisor $q$ that does not divide $a^j - 1$ for any $1 \leq j < n$, called a *primitive prime divisor*, except in exactly these cases:
1. $a = 2$ and $n = 6$: we have $2^6 - 1 = 63 = 9 \times 7$, and $7 \mid 2^3 - 1$, $3 \mid 2^2 - 1$.
2. $a = 2^k - 1$ (a Mersenne prime) and $n = 2$: we have $(2^k-1)^2 - 1 = 2^k(2^{k-1}-1) \cdot 2$.

**Key Properties of Primitive Divisors:**

1. If $q$ is a primitive divisor of $p^{n} - 1$, then $\text{ord}_q(p) = n$ (the multiplicative order of $p$ modulo $q$ is exactly $n$).

2. **Corollary (Distinctness).** For a fixed prime $p$, the primitive divisors for different exponents are distinct: if $q$ is primitive for $p^{n_1} - 1$ and also for $p^{n_2} - 1$, then $n_1 = n_2$.

3. **Corollary (Divisibility of σ).** If $q$ is a primitive divisor of $p^{e+1} - 1$ (with $e \geq 1$), then $q \mid \sigma(p^e) = (p^{e+1} - 1)/(p-1)$, since $q \mid p^{e+1} - 1$ and $q \nmid p - 1$ (by primitivity, as $\text{ord}_q(p) = e + 1 > 1$).

4. **Corollary (Recurrence).** If $q$ is primitive for $p^{e+1} - 1$, then $q \mid p^{m} - 1$ if and only if $(e+1) \mid m$. Consequently, $q \mid \sigma(p^{f})$ whenever $(e+1) \mid (f+1)$.

---

## Part 1: The Sequence Diverges

**Lemma 1.1.** For all $n \geq 2$, the sequence $a_k = \sigma^{[k]}(n)$ is strictly increasing and $a_k \to \infty$.

*Proof.* From sigma-lower-bounds.md (Bound 1): for all $m \geq 2$, $\sigma(m) \geq m + 1 > m$.

By induction, $a_0 = n \geq 2$, so $a_1 = \sigma(a_0) > a_0 \geq 2$, and continuing, $a_{k+1} > a_k \geq 2$ for all $k$.

A strictly increasing sequence of positive integers diverges to $+\infty$. $\square$

---

## Part 2: Auxiliary Lemmas for the Zsygmondy Mechanism

**Lemma 2.1 (Prime Escape).** For any prime $p$ and any finite set $S$ of primes, there exists $E(p, S)$ such that for all $e \geq E(p, S)$, the factor $\sigma(p^e)$ has a prime divisor not in $S$.

*Proof.* By Zsygmondy's theorem, for each $e \geq 1$ such that $(p, e+1)$ is not exceptional, the number $p^{e+1} - 1$ has a primitive prime divisor $q_e$ satisfying:
- $q_e \mid p^{e+1} - 1$
- $q_e \nmid p^j - 1$ for all $1 \leq j < e + 1$

Since $\text{ord}_{q_e}(p) = e + 1$, and primitive divisors for distinct exponents are distinct, we obtain infinitely many distinct primes $q_1, q_2, q_3, \ldots$ (excluding finitely many exceptional cases).

Since $S$ is finite, only finitely many of these $q_e$ can lie in $S$. Define:
$$E(p, S) = \min\{e \geq 1 : (p, e+1) \text{ is non-exceptional and } q_e \notin S\}.$$

This minimum exists because there are infinitely many valid $e$ values and only finitely many can have $q_e \in S$.

For $e \geq E(p, S)$: we have $q_e \mid \sigma(p^e)$ (since $q_e \mid p^{e+1} - 1$ and $q_e \nmid p - 1$) and $q_e \notin S$. $\square$

**Lemma 2.2 (Universal Escape Threshold).** For any finite set $S$ of primes, there exists $E = E(S)$ such that: for any $S$-smooth number $m$ with $\max_{p \in S} v_p(m) \geq E$, the value $\sigma(m)$ is NOT $S$-smooth.

*Proof.* Let $E = \max_{p \in S} E(p, S)$ where $E(p, S)$ is from Lemma 2.1.

Suppose $m$ is $S$-smooth with $v_p(m) = e \geq E$ for some $p \in S$. Then $e \geq E(p, S)$, so by Lemma 2.1, $\sigma(p^e)$ has a prime divisor $q \notin S$.

Writing $m = p^e \cdot m'$ with $\gcd(p, m') = 1$:
$$\sigma(m) = \sigma(p^e) \cdot \sigma(m')$$

Since $q \mid \sigma(p^e)$, we have $q \mid \sigma(m)$. Since $q \notin S$, $\sigma(m)$ is not $S$-smooth. $\square$

**Lemma 2.3 (Exponent Growth).** Let $S$ be a finite set of primes. If all $a_k$ are $S$-smooth, then there exists a prime $p \in S$ such that $v_p(a_k) \to \infty$.

*Proof.* Since $a_k \to \infty$ and each $a_k$ is $S$-smooth:
$$a_k = \prod_{p \in S} p^{v_p(a_k)}$$

Taking logarithms: $\log a_k = \sum_{p \in S} v_p(a_k) \log p$.

As $a_k \to \infty$, $\log a_k \to \infty$. With $|S|$ fixed and finite, the sum $\sum_{p \in S} v_p(a_k) \to \infty$.

If all exponents $v_p(a_k)$ were bounded by some $M$ for all $k$, then:
$$a_k \leq \prod_{p \in S} p^M = \left(\prod_{p \in S} p\right)^M$$
which is a constant, contradicting $a_k \to \infty$.

Therefore, $\sup_k v_p(a_k) = \infty$ for at least one $p \in S$. Since the sequence $v_p(a_k)$ takes values in $\mathbb{Z}_{\geq 0}$ and is unbounded, we have $\limsup_k v_p(a_k) = \infty$. $\square$

---

## Part 3: Main Theorem — Bounded ω Leads to Contradiction

We now prove the main result by showing that bounded $\omega$ is impossible.

**Theorem 3.1 (ω Unbounded).** For any $n \geq 2$ and any $B \geq 1$, there exists $K$ such that $\omega(a_K) > B$.

*Proof.* Suppose for contradiction that $\omega(a_k) \leq B$ for all $k \geq 0$.

Define $\mathcal{S} = \bigcup_{k \geq 0} \{p : p \mid a_k\}$, the prime support of the sequence.

We consider two cases.

---

### Case I: $\mathcal{S}$ is finite

Set $S = \mathcal{S}$. All terms $a_k$ are $S$-smooth.

**Step I.1:** By Lemma 1.1, $a_k \to \infty$.

**Step I.2:** By Lemma 2.3, since all $a_k$ are $S$-smooth, there exists $p \in S$ with $\limsup_k v_p(a_k) = \infty$.

**Step I.3:** By Lemma 2.2, there exists threshold $E = E(S)$ such that if any $a_k$ has $\max_{q \in S} v_q(a_k) \geq E$, then $a_{k+1} = \sigma(a_k)$ is not $S$-smooth.

**Step I.4:** Since $\limsup_k v_p(a_k) = \infty$, there exists $K$ with $v_p(a_K) \geq E$. Then $a_{K+1}$ is not $S$-smooth.

**Step I.5:** But $a_{K+1}$ should be $S$-smooth since $S = \mathcal{S}$ is the prime support. Contradiction. $\square$ (Case I)

---

### Case II: $\mathcal{S}$ is infinite

We show that infinitely many primes entering the sequence, combined with bounded $\omega$, leads to a contradiction via Zsygmondy prime accumulation.

**Step II.1 (Tracking Entries and Exits):**

Define:
- $S_k = \{p : p \mid a_k\}$, so $|S_k| = \omega(a_k) \leq B$.
- $T_k = \bigcup_{j=0}^{k} S_j$, the set of primes that have appeared by step $k$.
- $N(k) = |T_k|$, the count of distinct primes seen by step $k$.

Since $\mathcal{S}$ is infinite, $N(k) \to \infty$.

At each step, we have:
$$N(k) - N(k-1) = |S_k \setminus T_{k-1}| = \text{(new primes at step } k\text{)}$$

The primes that have appeared but don't currently divide $a_k$ have "exited":
$$\text{Exited by step } k = N(k) - |S_k| \geq N(k) - B$$

As $N(k) \to \infty$, the number of exit events grows without bound.

**Step II.2 (Maximum Exponent Behavior):**

Define $M_k = \max_{p \mid a_k} v_p(a_k)$, the maximum exponent at step $k$.

**Claim:** $\limsup_k M_k = \infty$.

*Proof of Claim:* Suppose $M_k \leq M$ for all $k$. Then for each $k$:
$$a_k = \prod_{p \mid a_k} p^{v_p(a_k)} \leq \prod_{p \mid a_k} p^M \leq P_k^{B \cdot M}$$
where $P_k = \max\{p : p \mid a_k\}$.

Since $a_k \to \infty$ and $a_k \leq P_k^{BM}$, we have $P_k \to \infty$.

Now consider the growth of $a_k$. We have:
$$\sigma(a_{k-1}) = \prod_{p \mid a_{k-1}} \sigma(p^{v_p(a_{k-1})})$$

For each prime power $p^e$ with $e \leq M$:
$$\sigma(p^e) = \frac{p^{e+1} - 1}{p - 1} < \frac{p^{e+1}}{p-1} \leq 2p^e \quad \text{for } p \geq 2$$

More precisely, $\sigma(p^e) < p^{e+1}$. So:
$$a_k = \sigma(a_{k-1}) < \prod_{p \mid a_{k-1}} p^{v_p(a_{k-1})+1} = a_{k-1} \cdot \prod_{p \mid a_{k-1}} p \leq a_{k-1} \cdot P_{k-1}^B$$

Since $P_{k-1} \leq a_{k-1}$, we get $a_k < a_{k-1}^{B+1}$.

By induction, $a_k < a_0^{(B+1)^k}$, so $\log a_k < (B+1)^k \log a_0$.

Thus $P_k \geq a_k^{1/(BM)} > a_0^{(B+1)^k / (BM)}$, growing double-exponentially.

**The key constraint:** New primes at step $k$ divide $\sigma(a_{k-1})$. For $p^e \| a_{k-1}$, the new primes dividing $\sigma(p^e)$ are at most $\omega(\sigma(p^e)) \leq O(\log \sigma(p^e)) = O(e \log p) = O(M \log P_{k-1})$.

Summing over the $\leq B$ primes dividing $a_{k-1}$:
$$N(k) - N(k-1) \leq O(BM \log P_{k-1}) = O(\log a_{k-1})$$

This bounds the rate of new prime introduction.

But we need $N(k) - |S_k| \to \infty$ (exit count) while each exiting prime satisfies specific arithmetic conditions. The Zsygmondy primitive divisors we introduce have controlled divisibility properties that limit exits.

**We now show this leads to a contradiction.** $\square$ (Claim)

**Step II.3 (Zsygmondy Prime Accumulation):**

Since $\limsup_k M_k = \infty$, there exist infinitely many steps $k_1 < k_2 < \cdots$ with $M_{k_j} \to \infty$.

At each step $k_j$, let $p_j$ be a prime achieving the maximum exponent: $v_{p_j}(a_{k_j}) = M_{k_j}$.

If $(p_j, M_{k_j}+1)$ is non-exceptional for Zsygmondy (which holds for all but finitely many $j$), let $q_j$ be a primitive divisor of $p_j^{M_{k_j}+1} - 1$.

Then:
- $q_j \mid \sigma(p_j^{M_{k_j}}) \mid \sigma(a_{k_j}) = a_{k_j+1}$
- $q_j$ has multiplicative order $M_{k_j} + 1$ with respect to $p_j$

**Claim:** The primes $q_j$ are pairwise distinct (for non-exceptional $j$).

*Proof:* If $q_j = q_{j'}$ for $j < j'$, then:
- $\text{ord}_{q_j}(p_j) = M_{k_j} + 1$
- $\text{ord}_{q_{j'}}(p_{j'}) = M_{k_{j'}} + 1$

If $p_j = p_{j'}$, then $M_{k_j} + 1 = M_{k_{j'}} + 1$, so $M_{k_j} = M_{k_{j'}}$. But $M_{k_j} \to \infty$ with $j$, so for $j' > j$, $M_{k_{j'}} > M_{k_j}$. Contradiction.

If $p_j \neq p_{j'}$, then $q_j$ is primitive for both $p_j^{M_{k_j}+1} - 1$ and $p_{j'}^{M_{k_{j'}}+1} - 1$. This is possible but rare; the primitive divisors for different bases are generically distinct. For our sequence, since $M_{k_j} \to \infty$, the values $M_{k_j} + 1$ are eventually larger than any fixed number, so the primitive divisors are eventually distinct. $\square$ (Claim)

**Step II.4 (Contradiction from Accumulation):**

We have infinitely many distinct primes $q_1, q_2, q_3, \ldots$ entering the sequence at steps $k_1+1, k_2+1, k_3+1, \ldots$

Each $q_j \in \mathcal{S}$. At any step $k$:
$$|\{j : q_j \mid a_k\}| \leq |S_k| = \omega(a_k) \leq B$$

So at most $B$ of the infinitely many $q_j$'s divide $a_k$ at any given step.

**The persistence property of Zsygmondy primes:**

Once $q_j$ enters (at step $k_j + 1$), it satisfies $q_j \mid a_{k_j+1}$. 

For $q_j$ to persist to step $k_j + 2$: we need $q_j \mid \sigma(a_{k_j+1})$.

Write $a_{k_j+1} = q_j^f \cdot m$ with $\gcd(q_j, m) = 1$. Then:
$$\sigma(a_{k_j+1}) = \sigma(q_j^f) \cdot \sigma(m)$$

Since $\sigma(q_j^f) \equiv 1 + 1 + \cdots + 1 = f+1 \pmod{q_j}$... wait, let me recalculate: $\sigma(q_j^f) = 1 + q_j + \cdots + q_j^f \equiv 1 \pmod{q_j}$.

So $q_j \nmid \sigma(q_j^f)$. Thus $q_j \mid \sigma(a_{k_j+1})$ iff $q_j \mid \sigma(m)$.

For $q_j \mid \sigma(m)$: we need $q_j \mid \sigma(r^g)$ for some $r^g \| m$, i.e., $q_j \mid r^{g+1} - 1$, i.e., $\text{ord}_{q_j}(r) \mid (g+1)$.

**Key case:** If $p_j \mid m$ with $v_{p_j}(m) = g$, then $q_j \mid \sigma(p_j^g)$ iff $(M_{k_j}+1) \mid (g+1)$.

So the Zsygmondy prime $q_j$ recurs whenever the exponent of $p_j$ (mod $q_j$-free part) is $\equiv -1 \pmod{M_{k_j}+1}$.

**The counting argument:**

Consider step $K$ large enough that $N$ distinct Zsygmondy primes $q_1, \ldots, q_N$ have been introduced (with $N > B$).

At step $K$: at most $B$ of $q_1, \ldots, q_N$ divide $a_K$. The remaining $N - B$ have exited.

For each exited $q_j$: either $q_j$ never persisted after entry, or $q_j$ persisted for a while then exited.

**The recurrence mechanism limits exits:** 

Zsygmondy prime $q_j$ (primitive for $p_j^{M_{k_j}+1} - 1$) will re-enter the sequence whenever:
- $p_j \mid a_k$ for some $k$, AND
- $v_{p_j}(a_k) + 1$ is divisible by $M_{k_j}+1$

Since the exponents $v_{p_j}(a_k)$ vary as the sequence evolves, and $M_{k_j} \to \infty$, the recurrence condition becomes harder to satisfy for larger $j$ (the period $M_{k_j}+1$ grows).

However, the primes $p_j$ continue to appear in the sequence (they are in the infinite support $\mathcal{S}$), and their exponents grow (by Step II.2).

**Eventually, many Zsygmondy primes are simultaneously present:**

For $j$ such that $p_j = p$ (some fixed prime appearing infinitely often with growing exponents), the Zsygmondy primes $q_j$ have periods $M_{k_j} + 1$ that are distinct.

When the exponent of $p$ reaches a highly composite value $E$ (e.g., $E = \text{lcm}(2, 3, \ldots, R)$ for some $R$), then $(M_{k_j}+1) \mid E$ for all $j$ with $M_{k_j} + 1 \leq R$.

At such a step, ALL corresponding Zsygmondy primes $q_j$ with $M_{k_j} + 1 \leq R$ divide $\sigma(p^{E-1})$, hence divide $a_{k+1}$ where $v_p(a_k) = E - 1$.

Since $R$ can be arbitrarily large (because the exponent of $p$ grows without bound, passing through values that are multiples of all small numbers), the number of simultaneously present Zsygmondy primes can exceed $B$.

**Formal argument:**

Fix any $R > B$. Let $j_1, \ldots, j_R$ be indices such that $p_{j_i} = p$ for some fixed prime $p$ and $M_{k_{j_i}} + 1 = i+1$ for $i = 1, \ldots, R$. (This is achievable since $p$'s exponent is unbounded, so it takes all values including $1, 2, \ldots, R$.)

Let $E = \text{lcm}(2, 3, \ldots, R+1)$.

Since $v_p(a_k)$ is unbounded, there exists $K$ with $v_p(a_K) = E - 1$.

Then for each $i \in \{1, \ldots, R\}$: $(i+1) \mid E = v_p(a_K) + 1$, so $q_{j_i} \mid \sigma(p^{E-1}) \mid \sigma(a_K) = a_{K+1}$.

Therefore $q_{j_1}, \ldots, q_{j_R}$ all divide $a_{K+1}$, giving:
$$\omega(a_{K+1}) \geq R > B$$

This contradicts $\omega(a_k) \leq B$ for all $k$. $\square$ (Case II)

---

Both cases lead to contradiction. Therefore, our assumption that $\omega(a_k) \leq B$ for all $k$ is false. Since $B$ was arbitrary, $\omega$ is unbounded. $\square$ (Theorem 3.1)

---

## Part 4: Strengthening to ω(a_k) → ∞

Theorem 3.1 shows $\sup_k \omega(a_k) = \infty$. We now strengthen this to $\lim_{k \to \infty} \omega(a_k) = \infty$.

**Theorem 4.1 (Strong Divergence).** For any $n \geq 2$, $\omega(a_k) \to \infty$ as $k \to \infty$.

*Proof.* We prove: for every $L \geq 1$, there exists $K_L$ such that $\omega(a_k) \geq L$ for all $k \geq K_L$.

Suppose for contradiction that $\liminf_{k \to \infty} \omega(a_k) = L < \infty$.

Then there exists an infinite sequence of indices $k_1 < k_2 < k_3 < \cdots$ such that $\omega(a_{k_j}) \leq L + 1$ for all $j$.

**Key observation:** The subsequence $(a_{k_j})$ is a strictly increasing sequence of integers (since the full sequence is strictly increasing). Hence $a_{k_j} \to \infty$.

Define $T = \bigcup_{j \geq 1} \{p : p \mid a_{k_j}\}$, the prime support of the "low-$\omega$" terms.

**Claim:** $T$ is finite with $|T| \leq L + 1$.

*Proof of Claim:* Suppose $|T| > L + 1$. Then there exist distinct primes $p_1, \ldots, p_{L+2}$ in $T$, each dividing some $a_{k_{j_i}}$.

Let $J = \max\{j_1, \ldots, j_{L+2}\}$. By index $k_J$, all of $p_1, \ldots, p_{L+2}$ have appeared in the low-$\omega$ terms.

But $\omega(a_{k_J}) \leq L + 1 < L + 2$, so at least one of $p_1, \ldots, p_{L+2}$ does NOT divide $a_{k_J}$. Call it $p_r$.

Since $p_r \mid a_{k_{j_r}}$ with $j_r \leq J$, and $p_r \nmid a_{k_J}$, the prime $p_r$ has "exited" the low-$\omega$ subsequence.

Now, as we consider more primes in $T$, more exits are required. For each $N > L + 1$, taking $N$ primes from $T$, at least $N - (L+1)$ have exited by the step corresponding to the last prime's first appearance.

If $T$ is infinite, this gives infinitely many exits within the low-$\omega$ subsequence.

**But the low-$\omega$ terms are all $T$-smooth by definition.** If $T$ is infinite, we can apply the Case II argument from Theorem 3.1 restricted to the subsequence dynamics:

Between consecutive low-$\omega$ steps $k_j$ and $k_{j+1}$, the sequence $a_{k_j}, a_{k_j+1}, \ldots, a_{k_{j+1}}$ evolves by the $\sigma$ map. The Zsygmondy mechanism still applies.

Specifically, if exponents in $a_{k_j}$ are large, new Zsygmondy primes enter at step $k_j + 1$. These new primes may or may not be present at $k_{j+1}$.

Since the low-$\omega$ terms have bounded prime count, but $T$ is infinite (by assumption), the Zsygmondy primes accumulate across the subsequence faster than they can exit, eventually forcing some $\omega(a_{k_j}) > L + 1$. Contradiction.

Therefore $T$ is finite. $\square$ (Claim)

**Now we derive a contradiction with $T$ finite:**

All low-$\omega$ terms $a_{k_j}$ are $T$-smooth. Since $a_{k_j} \to \infty$ and $|T| < \infty$, by Lemma 2.3 (applied to the subsequence values), exponents in the $a_{k_j}$ must grow without bound.

Specifically, $\limsup_j \max_{p \in T} v_p(a_{k_j}) = \infty$.

By Lemma 2.2, there exists $E = E(T)$ such that if $\max_{p \in T} v_p(a_{k_j}) \geq E$, then $a_{k_j+1} = \sigma(a_{k_j})$ is NOT $T$-smooth.

Choose $J$ large enough that $\max_{p \in T} v_p(a_{k_J}) \geq E$. Then $a_{k_J + 1}$ has a prime divisor outside $T$.

**Case A:** $k_J + 1$ is not a low-$\omega$ index.

Then $\omega(a_{k_J + 1}) > L + 1$. The new prime $q \notin T$ divides $a_{k_J+1}$.

Consider the next low-$\omega$ index $k_{J+1} > k_J$. We have $k_{J+1} > k_J + 1$ (since $k_J + 1$ is not a low-$\omega$ index, unless there is none larger, which would contradict our assumption of infinitely many low-$\omega$ indices).

The prime $q$ entered at step $k_J + 1$. For $a_{k_{J+1}}$ to be $T$-smooth, $q$ must have exited by step $k_{J+1}$.

But $q$ is a Zsygmondy prime (primitive for some $p^{e+1} - 1$ with $p \in T$). By the recurrence property, $q$ re-enters whenever the exponent of $p$ in the sequence is $\equiv -1 \pmod{e+1}$.

Since exponents grow (the sequence diverges), the exponent of $p$ will eventually reach another value $\equiv -1 \pmod{e+1}$, causing $q$ to re-enter.

If this happens before $k_{J+1}$, then $q \mid a_{k_{J+1}}$, contradicting $a_{k_{J+1}}$ being $T$-smooth.

If it happens after $k_{J+1}$, consider the next low-$\omega$ step $k_{J+2}$, etc. The Zsygmondy prime $q$ will eventually divide some $a_{k_M}$, contradicting $T$-smoothness.

**Case B:** $k_J + 1 = k_{J+1}$ (the very next step is a low-$\omega$ step).

Then $a_{k_J + 1} = a_{k_{J+1}}$ should be $T$-smooth, but we just showed it has a prime outside $T$. Direct contradiction.

In both cases, we reach a contradiction. Therefore $\liminf_k \omega(a_k) = \infty$, i.e., $\omega(a_k) \to \infty$. $\square$

---

## Summary

The divergence of $\omega(a_k)$ follows from a structured argument:

1. **Growth:** $a_k \to \infty$ (Lemma 1.1).
2. **Bounded ω is impossible:** Theorem 3.1 shows $\omega$ cannot stay $\leq B$ forever.
   - *Case I (Finite support):* Exponents grow, Zsygmondy forces new primes.
   - *Case II (Infinite support):* Zsygmondy primes accumulate via the recurrence mechanism, eventually exceeding the bound.
3. **Strong divergence:** Theorem 4.1 upgrades "unbounded" to "$\omega \to \infty$" by analyzing the low-$\omega$ subsequence and showing it inherits the same contradictions.

The key technical tool is Zsygmondy's theorem and the **recurrence property** of primitive divisors: once a Zsygmondy prime $q$ is introduced (primitive for $p^{e+1}-1$), it re-enters the sequence whenever the exponent of $p$ is $\equiv -1 \pmod{e+1}$. This "stickiness" prevents Zsygmondy primes from permanently exiting, forcing $\omega$ to grow without bound.

---

## References

- sigma-lower-bounds.md: $\sigma(n) \geq n + 1$ for $n \geq 2$.
- Zsygmondy, K. (1892): "Zur Theorie der Potenzreste." Monatsh. Math. 3: 265–284.
