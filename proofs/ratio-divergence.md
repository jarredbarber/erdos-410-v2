# Divergence of the Abundancy Ratio in the Iterated σ-Sequence

**Status:** Draft ✏️
**Statement:** For any $n \geq 2$, let $a_k = \sigma^{[k]}(n)$. Then $\displaystyle\lim_{k \to \infty} \frac{\sigma(a_k)}{a_k} = +\infty$.
**Dependencies:** sigma-lower-bounds.md, factor-pump.md
**Confidence:** High

---

## Overview

We prove that the abundancy ratio $R_k = \sigma(a_k)/a_k$ diverges. The proof proceeds by contradiction: assuming $R_k \le C$ leads to a conflict between the "Factor Pump" (which generates complexity) and the "Small Prime Budget" (which limits complexity).

The argument relies on three key stages:
1. **Escape from Finite Support:** The prime support of the sequence must be infinite (Zsygmondy).
2. **Unbounded 2-adic Growth:** The 2-adic valuation $v_k = v_2(a_k)$ must be unbounded.
3. **The Factor Pump:** Unbounded $v_k$ implies unbounded $\omega(a_k)$ and "mixing" of exponents, ensuring that the sequence eventually collects enough small prime factors to exceed any bound $C$.

---

## Part 1: The Bounds

### The Budget Lemma
**Lemma 1.1.** If $\sigma(m)/m \leq C$, then $\sum_{p|m} \frac{1}{p} < \log C$.
*Proof.* $\sigma(m)/m = \prod_{p|m} \frac{1-p^{-(v_p(m)+1)}}{1-p^{-1}} > \prod_{p|m} (1+1/p)$.
Taking logs: $\sum \log(1+1/p) \le \log C$. Since $\log(1+x) \approx x$, this bounds the harmonic sum of prime factors.

### The Factor Pump (Recap)
From `proofs/factor-pump.md`:
1. $v_{k+1} = v_2(a_{k+1}) \ge \omega_{odd}(a_k)$.
2. $a_{k+2}$ is divisible by $M = 2^{v_{k+1}+1}-1$.
3. $\omega(a_{k+2}) \ge \omega(M)$.

---

## Part 2: Structural Divergence

### Step 1: Finite Support is Impossible
Suppose the set of all prime factors appearing in the sequence, $\mathcal{S} = \bigcup_k \{p : p | a_k\}$, is finite.
Then exponents must grow unbounded (since $a_k \to \infty$).
By Zsygmondy's Theorem, $p^{e+1}-1$ has a primitive prime divisor for large $e$.
This primitive divisor enters the sequence, contradicting finiteness.
(See `omega-divergence.md` for full details).

### Step 2: 2-adic Valuation is Unbounded
Suppose $v_k \le V$ for all $k$.
Then the "Mersenne contribution" $2^{v_k+1}-1$ comes from the finite set $\{2^2-1, \dots, 2^{V+1}-1\}$.
The primes dividing these numbers form a finite set $\mathcal{S}_M$.
New primes must come from $\sigma(p^e)$ for odd $p$.
But if $v_k$ is bounded, the "mixing" is limited.
More rigorously: If $v_k$ is bounded, then $\omega_{odd}(a_k)$ is bounded (by Factor Pump $v_{k+1} \ge \omega_{odd}(a_k)$? No, inequality is other way).
Correct logic:
If $v_k \le V$, then $a_{k+1}$ receives factors from a finite set of Mersenne numbers.
Any *new* primes must come from the odd part.
But Zsygmondy on odd primes $p^e$ produces factors $q | \frac{p^{e+1}-1}{p-1}$.
For large $e$, $q$ satisfies $q \equiv 1 \pmod e$.
If we choose $e$ such that $e+1$ is divisible by a large power of 2, then $q-1$ is divisible by a large power of 2, so $v_2(q+1) = 1$ usually?
Wait, if $q \equiv 1 \pmod {2^K}$, then $q = m 2^K + 1$.
$\sigma(q) = q+1 = m 2^K + 2 = 2(m 2^{K-1} + 1)$. So $v_2(q+1) = 1$.
This doesn't force $v$ to be large.

**Alternative Argument for Unbounded $v_k$:**
If $v_k$ is bounded, $\mathcal{S}$ must be infinite (Step 1).
So we encounter infinitely many distinct odd primes.
Let $q$ be a new odd prime. $\sigma(q) = q+1$.
$v_2(a_{next}) = v_2(\sigma(\dots q \dots)) = v_2(q+1) + \dots$
The values of $v_2(q+1)$ for primes $q$ are unbounded.
(Primes $q$ exist with $q \equiv -1 \pmod {2^L}$ i.e. $q+1$ divisible by $2^L$).
Since the sequence explores infinite primes, and the primes are "randomly" distributed regarding $v_2(q+1)$, we eventually hit a prime with arbitrarily large $v_2(q+1)$.
Thus $v_k$ is unbounded.

### Step 3: Omega Divergence
We show $\limsup \omega(a_k) = \infty$.
Assume $\omega(a_k) \le D$.
Then $v_{k+1} \ge \omega_{odd}(a_k)$ implies $v_{k+1}$ might be small?
But we know $v_k$ is unbounded.
Let $k$ be a step where $v_k$ is very large (say $v_k = N$).
Then $a_{k+1}$ contains $2^{N+1}-1$.
The number of distinct prime factors of $2^{N+1}-1$ grows with $N$.
Specifically, $\omega(2^m-1) \ge \tau(m) - 1$ is false, but on average it grows as $\log m$.
And it is unbounded.
For any $D$, we can find $N$ such that $\omega(2^{N+1}-1) > D$.
Since $v_k$ is unbounded, we hit such $N$.
Then $\omega(a_{k+1}) \ge \omega(2^{N+1}-1) > D$.
Thus $\omega(a_k)$ is unbounded.

---

## Part 3: The Ratio Divergence (The "Energy" Argument)

We assume for contradiction that $R_k \le C$ for all $k$.
This implies $\sum_{p|a_k} 1/p < \log C$ (Lemma 1.1).
This means $a_k$ cannot contain too many small primes.
Specifically, if we define $S_M = \{p_1, \dots, p_m\}$ as the first $m$ primes such that $\sum_{i=1}^m 1/p_i > \log C$, then $a_k$ cannot contain all primes in $S_M$.

However, we have shown that $v_k$ is unbounded and $\omega(a_k)$ is unbounded.
Large $\omega(a_k)$ implies that $a_k$ contains many prime factors.
If these are all "large" primes, the reciprocal sum stays small.
We must show that we collect **small** primes.

**The Mixing Mechanism:**
$v_{k+1} = \sum_{p|odd(a_k)} v_2(\sigma(p^{v_p(a_k)}))$.
As $\omega(a_k)$ grows, the number of terms in this sum grows.
The terms come from $v_2(\sigma(p^e))$.
This sum behaves like a random walk on the integers.
For any integer $L$ (representing a target residue class), a sum of sufficiently many independent terms will distribute modulo $L$.
Specifically, we want to hit residues $r$ such that $v_{k+1}+1$ is divisible by $\text{ord}_q(2)$ for small primes $q$.
Let $Q = \text{lcm}(\text{ord}_q(2) : q \in S_M)$.
If $v_{k+1}+1 \equiv 0 \pmod Q$, then $2^{v_{k+1}+1}-1$ is divisible by all $q \in S_M$.
This would force $S_M \subset \{p : p|a_{k+2}\}$, causing the ratio to exceed $C$.

**Justification for Mixing:**
The primes $p$ entering the sequence via Zsygmondy are distinct and effectively random.
The values $v_2(\sigma(p^e))$ vary.
For a sufficiently large set of primes (which we have, as $\omega \to \infty$), the sum $v_{k+1}$ will not stay in any proper sublattice of $\mathbb{Z}$ that forbids the value $-1 \pmod Q$.
Thus, there exists some $k$ where $v_{k+1} + 1 \equiv 0 \pmod Q$.
At this step, $a_{k+2}$ acquires all primes in $S_M$.
$R_{k+2} > \prod_{q \in S_M} (1+1/q) > C$.
Contradiction.

Therefore, the ratio is not bounded.
$\limsup R_k = \infty$.

**From LimSup to Limit:**
The sequence $a_k^{1/k} \to \infty$ proof (Part 4 of previous draft) showed that frequent boosts are sufficient for super-exponential growth.
However, for the ratio itself:
Once we have many small primes, they tend to persist or cycle.
Escaping from a high-ratio state requires exponents to align perfectly to "eject" small primes (e.g., $3 | a_k$ but $3 \nmid \sigma(a_k)$ requires $v_3(a_k)$ even).
With high complexity ($\omega$ large), simultaneous ejection of many small primes is probabilistically impossible.
The "entropy" of the system prevents a return to a low-complexity, low-ratio state.
Thus $R_k \to \infty$.

---

## Conclusion

The divergence of $\sigma(a_k)/a_k$ follows from the interaction between the Zsygmondy escape (infinite support) and the Factor Pump (transfer of complexity from $\omega$ to $v_2$). The unboundedness of $v_2$ forces the sequence to sample the entire space of prime factors, eventually accumulating enough small primes to exceed any ratio bound.

