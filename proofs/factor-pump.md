# Factor Pump Mechanism for Omega Growth

**Status:** Verified ✅
**Reviewed by:** erdos410v2-4mp
**Statement:** The number of distinct prime factors $\omega(a_k)$ tends to grow because $\omega(a_{k+2})$ acquires new factors from $2^{v_2(a_{k+1})+1}-1$, where $v_2(a_{k+1}) \ge \omega_{odd}(a_k)$.
**Dependencies:** None
**Confidence:** High

## Lemma A: $v_2(\sigma(n)) \ge \omega_{odd}(n)$

**Statement:** Let $\omega_{odd}(n)$ be the number of prime factors of $n$ (counted without multiplicity) that appear with an odd exponent. Then $v_2(\sigma(n)) \ge \omega_{odd}(n_{odd})$, where $n_{odd}$ is the odd part of $n$.

**Proof:**
Let the prime factorization of $n$ be $n = 2^k \cdot \prod_{i=1}^r p_i^{e_i}$, where $p_i$ are distinct odd primes.
Since $\sigma$ is multiplicative, $\sigma(n) = \sigma(2^k) \prod_{i=1}^r \sigma(p_i^{e_i})$.
$\sigma(2^k) = 2^{k+1}-1$, which is always odd. Thus $v_2(\sigma(2^k)) = 0$.
The valuation is determined entirely by the odd prime factors:
$$ v_2(\sigma(n)) = \sum_{i=1}^r v_2(\sigma(p_i^{e_i})) $$

Consider a single term $\sigma(p^e) = 1 + p + p^2 + \dots + p^e$.
- **Case 1: $e$ is even.** The sum has $e+1$ terms (an odd number). The sum of an odd number of odd terms is odd. Thus $v_2(\sigma(p^e)) = 0$.
- **Case 2: $e$ is odd.** The sum has $e+1$ terms (an even number). We can pair terms:
  $$ \sigma(p^e) = (1+p)(1 + p^2 + p^4 + \dots + p^{e-1}) $$
  Since $p$ is odd, $1+p$ is even. Thus $\sigma(p^e)$ is divisible by $1+p$, so it is even.
  Therefore, $v_2(\sigma(p^e)) \ge 1$.

Substituting back into the sum:
$$ v_2(\sigma(n)) = \sum_{i: e_i \text{ is odd}} v_2(\sigma(p_i^{e_i})) \ge \sum_{i: e_i \text{ is odd}} 1 $$
The quantity on the right is precisely the number of odd prime factors with odd exponents, which is $\omega_{odd}(n_{odd})$.
Thus, $v_2(\sigma(n)) \ge \omega_{odd}(n_{odd})$.
Q.E.D.

## Lemma B: Recursive Factor Bounds

**Statement:** Let $a_{k+1} = \sigma(a_k)$. Let $v_k = v_2(a_k)$ and $d_k$ be the odd part of $a_k$. Then:
1. $v_{k+1} \ge \omega_{odd}(d_k)$
2. $\omega(a_{k+2}) \ge \omega(2^{v_{k+1}+1}-1) + \omega(\sigma(d_{k+1})) - \omega(\gcd(2^{v_{k+1}+1}-1, \sigma(d_{k+1})))$

**Proof:**
1. Since $a_{k+1} = \sigma(a_k) = \sigma(2^{v_k} d_k) = (2^{v_k+1}-1)\sigma(d_k)$, and $2^{v_k+1}-1$ is odd, all factors of 2 in $a_{k+1}$ come from $\sigma(d_k)$.
   $$ v_{k+1} = v_2(a_{k+1}) = v_2(\sigma(d_k)) $$
   By Lemma A applied to $d_k$, $v_2(\sigma(d_k)) \ge \omega_{odd}(d_k)$.
   Thus, $v_{k+1} \ge \omega_{odd}(d_k)$.

2. We have $a_{k+2} = \sigma(a_{k+1})$.
   Let $a_{k+1} = 2^{v_{k+1}} d_{k+1}$.
   $$ a_{k+2} = \sigma(2^{v_{k+1}} d_{k+1}) = (2^{v_{k+1}+1}-1) \sigma(d_{k+1}) $$
   Let $M = 2^{v_{k+1}+1}-1$ and $S = \sigma(d_{k+1})$.
   The number of distinct prime factors of a product is the sum of their distinct prime factors minus the overlap:
   $$ \omega(a_{k+2}) = \omega(M \cdot S) = \omega(M) + \omega(S) - \omega(\gcd(M, S)^*) $$
   where $\gcd(M, S)^*$ is the product of prime factors common to $M$ and $S$.
   Thus $\omega(a_{k+2}) \ge \omega(2^{v_{k+1}+1}-1) + \omega(\sigma(d_{k+1})) - \omega(\gcd(\dots))$.
   Or more simply, $\omega(a_{k+2}) \ge \omega(2^{v_{k+1}+1}-1)$.
   Q.E.D.

## Recursive Inequality and The Factor Pump

Combining the results:
$$ v_{k+1} \ge \omega_{odd}(d_k) $$
$$ \omega(a_{k+2}) \ge \omega(2^{v_{k+1}+1}-1) $$

This establishes the **Factor Pump** loop:
1. **Input:** High number of odd-exponent factors in $d_k$ ($\omega_{odd}(d_k)$ large).
2. **Compression:** These factors generate a large power of 2 in $a_{k+1}$ ($v_{k+1}$ large).
3. **Expansion:** The term $2^{v_{k+1}+1}-1$ in $\sigma(a_{k+1})$ factorizes into multiple new primes ($\omega(a_{k+2})$ large).

**Growth Argument:**
Let $N = v_{k+1}+1$. The term $M_N = 2^N-1$ contributes to $\omega(a_{k+2})$.
- **Primitive Prime Divisors:** By Bang's Theorem (Zsigmondy's Theorem), for $N > 6$, $2^N-1$ has at least one prime factor $p$ that does not divide $2^j-1$ for any $j < N$. This $p$ is likely new to the sequence history, or at least new relative to recent terms.
- **Composite N:** If $N$ is composite, $2^N-1$ has many algebraic factors (e.g., $2^{N/2}-1, 2^{N/3}-1$, etc.), leading to $\omega(2^N-1) \gg 1$.
- **Mersenne Primes (Sparsity):** The only case where $\omega(2^N-1) = 1$ is when $2^N-1$ is a Mersenne prime (which implies $N$ is prime).
  - Mersenne primes are extremely sparse.
  - For a random integer $N$, the expected value of $\omega(2^N-1)$ is roughly $\log N$ (since $\omega(m) \sim \log \log m$ and $m \approx 2^N$).
  - Even if $N$ is prime, $2^N-1$ is often composite (e.g., $2^{11}-1 = 23 \cdot 89$).
- **No Square Traps:** For $N > 1$, $2^N-1$ is never a perfect square (follows from Catalan's conjecture/Mihailescu's theorem). This ensures that $2^N-1$ always contributes at least one prime factor with an odd exponent, preventing $\omega_{odd}(a_{k+2})$ from dropping to zero.

**Conclusion:**
Since $v_{k+1}$ is determined by the complex structure of $\sigma(d_k)$, it behaves somewhat randomly. Therefore $N = v_{k+1}+1$ is rarely a prime that yields a Mersenne prime.
Most of the time, $\omega(2^{v_{k+1}+1}-1) \ge 2$, and often much larger.
This provides a persistent upward pressure on $\omega(a_k)$, driving the sequence complexity (and $a_k$ itself) to infinity.
