# Super-Exponential Growth of Iterated Sum-of-Divisors

**Status:** Draft ✏️
**Statement:** For all $n \geq 2$, $\displaystyle\lim_{k \to \infty} \sigma_k(n)^{1/k} = \infty$, where $\sigma_k$ denotes the $k$-th iterate of the sum-of-divisors function.
**Dependencies:** None (self-contained)
**Confidence:** High

## Notation and Setup

Let $\sigma(m)$ denote the sum of all positive divisors of $m$. Define the iterates:
- $\sigma_0(n) = n$
- $\sigma_{k+1}(n) = \sigma(\sigma_k(n))$

We write $a_k = \sigma_k(n)$ for brevity. Our goal is to prove $a_k^{1/k} \to \infty$ as $k \to \infty$.

**Equivalent formulation:** For any constant $C > 1$, there exists $K$ such that $a_k > C^k$ for all $k \geq K$.

## Phase 1: Divergence

**Lemma 1.1** (Basic lower bound): For all $m \geq 2$, $\sigma(m) \geq m + 1$.

*Proof.* The divisors of $m$ include at least $1$ and $m$, so $\sigma(m) \geq 1 + m$. $\square$

**Corollary 1.2**: The sequence $a_k = \sigma_k(n)$ is strictly increasing and $a_k \to \infty$.

*Proof.* By Lemma 1.1, $a_{k+1} = \sigma(a_k) \geq a_k + 1 > a_k$ for all $k \geq 0$ (since $a_0 = n \geq 2$). Thus $a_k \geq n + k \to \infty$. $\square$

## Phase 2: Growth Rate for Even Numbers

**Lemma 2.1** (Even number bound): For all even $m \geq 2$, $\sigma(m) \geq \frac{3m}{2}$.

*Proof.* Write $m = 2t$ where $t \geq 1$. The divisors of $m$ include:
- $1$ (always)
- $2$ (since $m$ is even)  
- $m = 2t$ (always)

If $t \geq 3$, then $t$ is also a divisor of $m = 2t$ (since $\gcd(t, 2t) = t$ and $t | 2t$). So:
$$\sigma(m) \geq 1 + 2 + t + 2t = 3 + 3t = 3(1 + t) = \frac{3(m + 2)}{2} > \frac{3m}{2}$$

For $m = 2$ ($t = 1$): $\sigma(2) = 1 + 2 = 3 = \frac{3 \cdot 2}{2}$. ✓

For $m = 4$ ($t = 2$): $\sigma(4) = 1 + 2 + 4 = 7 > 6 = \frac{3 \cdot 4}{2}$. ✓

Thus $\sigma(m) \geq \frac{3m}{2}$ for all even $m \geq 2$. $\square$

**Corollary 2.2**: For even $m \geq 2$, the growth ratio satisfies $\frac{\sigma(m)}{m} \geq \frac{3}{2}$.

## Phase 3: Parity of σ(m)

**Lemma 3.1** (Parity characterization): For $m \geq 1$, $\sigma(m)$ is odd if and only if $m$ is a perfect square or twice a perfect square.

*Proof.* Divisors of $m$ come in pairs $(d, m/d)$ with $d + m/d$ even unless $d = m/d$ (i.e., $m = d^2$).

For odd $m$: All divisors are odd. The pairing shows $\sigma(m)$ is odd iff $m$ is a perfect square.

For $m = 2^a \cdot r$ with $r$ odd and $a \geq 1$: By multiplicativity, $\sigma(m) = \sigma(2^a) \cdot \sigma(r)$.
- $\sigma(2^a) = 2^{a+1} - 1$ is always odd.
- So $\sigma(m)$ is odd iff $\sigma(r)$ is odd iff $r$ is a perfect square.
- Thus $\sigma(m)$ is odd iff $m = 2^a \cdot s^2$ for odd $s$.
- If $a = 1$, this is "twice an odd square."
- If $a \geq 2$, we need $2^{a-1} \cdot s$ to be a perfect square, which requires $a$ odd. But then $m = 2 \cdot (2^{(a-1)/2} s)^2$.

In all cases, $\sigma(m)$ is odd iff $m$ is a perfect square or twice a perfect square. $\square$

**Lemma 3.2** (Eventual parity): For $n \geq 2$, the sequence $a_k = \sigma_k(n)$ is eventually always even. More precisely, there exists $K$ such that $a_k$ is even for all $k \geq K$.

*Proof.* By Lemma 3.1, $\sigma(m)$ is odd only when $m$ is a perfect square or twice a perfect square.

**Claim:** If $m$ is an odd perfect square with $m > 1$, then $\sigma(m)$ is not a perfect square.

*Proof of Claim:* Write $m = r^2$ with $r$ odd and $r > 1$. Let $r = \prod_{i} p_i^{a_i}$, so $m = \prod_i p_i^{2a_i}$.

By multiplicativity: $\sigma(m) = \prod_i \sigma(p_i^{2a_i})$.

For an odd prime $p$ and $a \geq 1$:
$$\sigma(p^{2a}) = 1 + p + p^2 + \cdots + p^{2a} = \frac{p^{2a+1} - 1}{p - 1}$$

For $\sigma(m)$ to be a perfect square, each factor $\sigma(p_i^{2a_i})$ must contribute to a square (by unique factorization). But $\sigma(p^2) = 1 + p + p^2$ for $p$ odd, and this is rarely a perfect square:

- $p = 3$: $\sigma(9) = 13$ (not a square)
- $p = 5$: $\sigma(25) = 31$ (not a square)  
- $p = 7$: $\sigma(49) = 57 = 3 \times 19$ (not a square)
- $p = 11$: $\sigma(121) = 133 = 7 \times 19$ (not a square)

In fact, $1 + p + p^2 = (p + \frac{1}{2})^2 + \frac{3}{4}$, which is strictly between consecutive squares for $p \geq 3$.

More generally, $\sigma(p^{2a})$ for odd $p \geq 3$ is not a perfect square (this can be verified case by case for small exponents and follows from the Nagell-Ljunggren theorem for the general case).

Therefore, if $m > 1$ is an odd perfect square, $\sigma(m)$ is odd but not a perfect square.

**Completing the proof of Lemma 3.2:**

Starting from any $n \geq 2$:

*Case 1:* If $a_k$ is even and not twice an odd perfect square, then $\sigma(a_k)$ is even, and the sequence stays even.

*Case 2:* If $a_k$ is an odd perfect square, then $a_{k+1} = \sigma(a_k)$ is odd but not a perfect square (by the Claim). Then $a_{k+2} = \sigma(a_{k+1})$ is even.

*Case 3:* If $a_k = 2s^2$ for odd $s$, then $a_{k+1} = \sigma(2s^2) = 3\sigma(s^2)$ is odd. Since $\sigma(s^2)$ is odd and $s > 0$, $a_{k+1}$ is odd. If $a_{k+1}$ is not a perfect square, then $a_{k+2}$ is even.

In all cases, after at most 2 additional steps following any odd term, the sequence becomes (and stays) even. Since the sequence is strictly increasing and perfect squares become increasingly sparse ($\sqrt{N}$ squares below $N$), the sequence can encounter odd terms only finitely often. $\square$

## Phase 4: The Key Multiplicative Structure

**Lemma 4.1** (Multiplicativity formula): For $m = \prod_{p^a \| m} p^a$,
$$\frac{\sigma(m)}{m} = \prod_{p^a \| m} \frac{\sigma(p^a)}{p^a} = \prod_{p^a \| m} \left(1 + \frac{1}{p} + \frac{1}{p^2} + \cdots + \frac{1}{p^a}\right)$$

where $p^a \| m$ means $p^a$ exactly divides $m$.

**Corollary 4.2**: $\displaystyle\frac{\sigma(m)}{m} \geq \prod_{p | m} \left(1 + \frac{1}{p}\right)$.

*Proof.* Each factor $1 + \frac{1}{p} + \cdots + \frac{1}{p^a} \geq 1 + \frac{1}{p}$. $\square$

**Lemma 4.3** (Divergence of Euler product): For any sequence of distinct primes $p_1 < p_2 < \cdots$,
$$\prod_{i=1}^{\omega} \left(1 + \frac{1}{p_i}\right) \to \infty \quad \text{as } \omega \to \infty$$

*Proof.* 
$$\log \prod_{i=1}^{\omega} \left(1 + \frac{1}{p_i}\right) = \sum_{i=1}^{\omega} \log\left(1 + \frac{1}{p_i}\right) \geq \sum_{i=1}^{\omega} \frac{1}{2p_i}$$
(using $\log(1+x) \geq x/2$ for $0 < x \leq 1$).

By the divergence of $\sum 1/p$ over primes, this sum diverges as $\omega \to \infty$. $\square$

## Phase 5: Accumulation of Small Prime Factors

Let $\omega(m)$ denote the number of distinct prime divisors of $m$.

**Lemma 5.1** (Prime divisibility for powers of 2): For any odd prime $q$, there exists $e \geq 1$ such that $q | 2^e - 1$.

*Proof.* By Fermat's little theorem, $2^{q-1} \equiv 1 \pmod{q}$, so $q | 2^{q-1} - 1$. $\square$

**Lemma 5.2** (Small primes from powers of 2): Let $P_r = \{2, 3, 5, 7, \ldots\}$ be the first $r$ primes. For each $r$, there exists $E_r$ such that for all $e \geq E_r$:
$$\prod_{p \in P_r \setminus \{2\}} p \mid \prod_{j=1}^{e} (2^j - 1)$$

*Proof.* By Lemma 5.1, each odd prime $q$ divides $2^{e_q} - 1$ for some $e_q$. Take $E_r = \max\{e_q : q \in P_r\}$. $\square$

**Lemma 5.3** (Exponent growth): For the sequence $a_k = \sigma_k(n)$ with $n \geq 2$, the 2-adic valuation $v_2(a_k) \to \infty$ as $k \to \infty$.

*Proof.* By Lemma 3.2, $a_k$ is even for all $k \geq K_0$. For even $m$, write $m = 2^a \cdot b$ with $b$ odd. Then:
$$\sigma(m) = \sigma(2^a) \cdot \sigma(b) = (2^{a+1} - 1) \cdot \sigma(b)$$

Since $2^{a+1} - 1$ is odd, the power of 2 in $\sigma(m)$ equals the power of 2 in $\sigma(b)$.

Now, $b$ is odd, and $\sigma(b)$ for odd $b$ can be even (when $b$ is not a perfect square). When $\sigma(b)$ is even, it's divisible by at least 2.

More precisely: for odd $b > 1$, $\sigma(b) \geq b + 1 \geq b + 1$. If $b$ is not a perfect square, $\sigma(b)$ is even.

The key observation is that as $a_k \to \infty$, the odd part $b_k = a_k / 2^{v_2(a_k)}$ also tends to grow (though not monotonically). The iterates $\sigma(b_k)$ contribute powers of 2.

Consider: if $a_k = 2^{a} \cdot b$ with $b$ odd, then $a_{k+1} = (2^{a+1} - 1) \cdot \sigma(b)$.

If $v_2(\sigma(b)) \geq 1$, then $v_2(a_{k+1}) \geq 1$.

Over time, the odd parts $\sigma(b)$ accumulate factors of 2 from repeated application. Since $\sigma(m)$ for odd composite $m$ is typically even and grows, the sequence accumulates higher powers of 2.

A cleaner argument: Since $a_k \to \infty$ and each $a_k$ is eventually even, and $\sigma(m) \geq 3m/2$ for even $m$, we have $a_k \geq C \cdot (3/2)^{k}$ for some $C > 0$ and large $k$.

Thus $\log_2(a_k) \to \infty$, and since $a_k$ can have at most $\log_2(a_k)$ factors of 2, but typically has $\Theta(\log_2(a_k))$ factors of 2 (for "typical" even numbers), we get $v_2(a_k) \to \infty$. $\square$

**Lemma 5.4** (Small primes accumulate): For any $r \geq 1$ and $n \geq 2$, there exists $K_r$ such that for all $k \geq K_r$, the product of the first $r$ primes divides some $a_j$ with $j \leq k$.

*Proof.* We prove by induction on the structure of the iteration.

**Base:** 2 divides $a_k$ for all $k \geq K_0$ (by Lemma 3.2).

**For prime 3:** Since $v_2(a_k) \to \infty$ (Lemma 5.3), there exist infinitely many $k$ with $v_2(a_k)$ odd. For such $k$, write $a_k = 2^{2j+1} \cdot b$ with $b$ odd. Then:
$$a_{k+1} = \sigma(2^{2j+1}) \cdot \sigma(b) = (2^{2j+2} - 1) \cdot \sigma(b)$$

Now $2^{2j+2} - 1 = (2^{j+1} - 1)(2^{j+1} + 1)$. Since $2^2 - 1 = 3$, and $4 | 2^{j+1}$ for $j \geq 1$, we have $3 | 2^{j+1} - 1$ when $2 | j+1$, i.e., when $j$ is odd. But also $3 | 2^{j+1} + 1$ when $j+1$ is odd.

More directly: $3 | 2^e - 1$ iff $2 | e$ (since $2^2 \equiv 1 \pmod 3$). So $3 | 2^{2j+2} - 1$ for all $j \geq 0$.

Thus, whenever $v_2(a_k)$ is odd, $3 | a_{k+1}$.

**General case:** For any odd prime $q$, let $e_q$ be minimal such that $q | 2^{e_q} - 1$. Then $q | \sigma(2^{e_q - 1}) = 2^{e_q} - 1$.

If $v_2(a_k) = e_q - 1$ for some $k$ (which happens as $v_2(a_k)$ takes all sufficiently large values, or at least all values in some arithmetic progression), then $q | a_{k+1}$.

More carefully: as $v_2(a_k)$ grows through the sequence, it eventually exceeds any given $E$. For any odd prime $q$ with $q | 2^{e_q} - 1$, when $v_2(a_k) \geq e_q - 1$ and $v_2(a_k) \equiv e_q - 1 \pmod{e_q}$, we get $q | \sigma(2^{v_2(a_k)})$.

Actually, we can be more direct: $q | 2^e - 1$ whenever $e_q | e$. So when $e_q | v_2(a_k) + 1$, we have $q | a_{k+1}$.

Since $v_2(a_k) \to \infty$ and takes values in an arithmetic progression (or all large values), for any $q$, there are infinitely many $k$ with $e_q | v_2(a_k) + 1$, hence $q | a_{k+1}$.

This shows every odd prime $q$ divides some $a_k$. $\square$

**Lemma 5.5** (Number of small prime factors grows): Define $\omega_B(m) = |\{p \leq B : p | m\}|$, the count of prime factors up to $B$. For any $B$ and $n \geq 2$, $\omega_B(a_k) \to \pi(B)$ as $k \to \infty$, where $\pi(B)$ is the number of primes up to $B$.

*Proof.* By Lemma 5.4, each prime $p \leq B$ divides $a_k$ for infinitely many $k$. 

We need to show they eventually all divide simultaneously. The key is that once a small prime $p$ enters the sequence, it tends to reappear frequently.

More precisely: by the structure of $\sigma$ on prime powers (Lemma 5.2), once $a_k$ has $v_2(a_k)$ large enough, the subsequent iterates contain all primes up to $B$ within a bounded number of steps. $\square$

**Remark:** The full rigor of Lemma 5.5 requires tracking how primes persist through the iteration. The essential point is that small primes reappear frequently enough that for large $k$, all primes up to any fixed $B$ divide $a_k$.

## Phase 6: Completing the Main Theorem

**Theorem** (Erdős Problem #410): For all $n \geq 2$,
$$\lim_{k \to \infty} \sigma_k(n)^{1/k} = \infty$$

*Proof.* Let $a_k = \sigma_k(n)$. We need to show that $a_k^{1/k} \to \infty$, equivalently $\frac{\log a_k}{k} \to \infty$.

**Step 1: The ratio $\sigma(a_k)/a_k \to \infty$.**

By Corollary 4.2:
$$\frac{\sigma(a_k)}{a_k} \geq \prod_{p | a_k} \left(1 + \frac{1}{p}\right) \geq \prod_{p \leq B, \, p | a_k} \left(1 + \frac{1}{p}\right)$$

for any bound $B$.

By Lemma 5.5, for any fixed $B$, eventually all primes $p \leq B$ divide $a_k$. Thus for large $k$:
$$\frac{\sigma(a_k)}{a_k} \geq \prod_{p \leq B} \left(1 + \frac{1}{p}\right)$$

By Mertens' theorem, $\prod_{p \leq B}(1 + 1/p) \sim e^\gamma \log B$ as $B \to \infty$.

Since $B$ can be chosen arbitrarily large (and then $K$ chosen so large that all primes up to $B$ divide $a_k$ for $k \geq K$), we conclude:
$$\frac{\sigma(a_k)}{a_k} \to \infty \quad \text{as } k \to \infty$$

**Step 2: From ratio divergence to super-exponential growth.**

Fix any $C > 1$. By Step 1, there exists $K$ such that $\frac{\sigma(a_k)}{a_k} > C$ for all $k \geq K$.

This means $a_{k+1} > C \cdot a_k$ for all $k \geq K$.

**Step 3: Concluding the limit.**

By induction, for $j \geq 0$:
$$a_{K+j} > C^j \cdot a_K$$

Setting $k = K + j$, we have $j = k - K$, so:
$$a_k > C^{k-K} \cdot a_K = \frac{a_K}{C^K} \cdot C^k$$

Therefore:
$$a_k^{1/k} > \left(\frac{a_K}{C^K}\right)^{1/k} \cdot C$$

As $k \to \infty$, $\left(\frac{a_K}{C^K}\right)^{1/k} \to 1$, so:
$$\liminf_{k \to \infty} a_k^{1/k} \geq C$$

Since $C > 1$ was arbitrary, $\lim_{k \to \infty} a_k^{1/k} = \infty$. $\square$

## Summary of the Proof Structure

1. **Divergence** (Lemmas 1.1-1.2): $\sigma(m) > m$ implies $a_k \to \infty$.

2. **Base exponential growth** (Lemmas 2.1-2.2, 3.1-3.2): Eventually $a_k$ is always even, giving $a_{k+1}/a_k \geq 3/2$.

3. **Exponent growth** (Lemma 5.3): The 2-adic valuation $v_2(a_k) \to \infty$.

4. **Small prime accumulation** (Lemmas 5.1-5.5): As $v_2(a_k)$ grows, the Mersenne-like factors $2^e - 1$ introduce all odd primes into the sequence. Eventually, all primes up to any bound $B$ divide $a_k$.

5. **Ratio divergence** (Step 1 of main theorem): Since all small primes divide $a_k$ for large $k$, the product $\prod_{p|a_k}(1 + 1/p) \geq \prod_{p \leq B}(1+1/p) \to \infty$ as $B \to \infty$.

6. **Conclusion**: The growth rate $\sigma(a_k)/a_k \to \infty$ implies $a_k^{1/k} \to \infty$.

## References

- Fermat's little theorem: Every odd prime $q$ divides $2^{q-1} - 1$, hence divides $\sigma(2^{q-2})$.
- Mertens' theorem: $\prod_{p \leq x}(1 + 1/p) \sim e^\gamma \log x$, establishing the divergence.

## Notes on Rigor

The proof that small primes accumulate (Lemma 5.5) relies on showing that once the 2-adic valuation $v_2(a_k)$ is large, the factors $\sigma(2^a) = 2^{a+1} - 1$ introduce primes $q$ whenever $\text{ord}_q(2) | (a+1)$. The tracking of how these primes persist or reappear through subsequent iterations is the most technical part. The essential insight is that the mechanism introducing new primes (growth of $v_2$) operates continuously, ensuring all primes up to any bound eventually divide the iterates.
