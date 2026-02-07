# Parity of the Sum-of-Divisors Function

**Status:** Verified ✅
**Reviewed by:** erdos410v2-ii5
**Statement:** For all $n \geq 1$, $\sigma(n)$ is odd if and only if $n$ is a perfect square or twice a perfect square. Equivalently, $\sigma(n)$ is odd if and only if the odd part of $n$ is a perfect square.
**Dependencies:** None (self-contained)
**Confidence:** Certain

## Proof

### Setup

Let $\sigma(n) = \sum_{d \mid n} d$ denote the sum of all positive divisors of $n$. We prove: for all $n \geq 1$,

$$\sigma(n) \equiv 1 \pmod{2} \quad \iff \quad n = k^2 \text{ or } n = 2k^2 \text{ for some } k \geq 1.$$

An equivalent formulation: $\sigma(n)$ is odd if and only if the odd part of $n$ (i.e., $n / 2^{v_2(n)}$) is a perfect square.

We use the **multiplicativity** of $\sigma$: if $n = p_1^{a_1} p_2^{a_2} \cdots p_r^{a_r}$ is the prime factorization of $n$, then

$$\sigma(n) = \prod_{i=1}^{r} \sigma(p_i^{a_i}),$$

where for each prime power $p^a$:

$$\sigma(p^a) = 1 + p + p^2 + \cdots + p^a = \frac{p^{a+1} - 1}{p - 1}.$$

Since $\sigma(n)$ is a product of integers, $\sigma(n)$ is odd if and only if every factor $\sigma(p_i^{a_i})$ is odd.

### Step 1: The factor $\sigma(2^a)$ is always odd

For $p = 2$ and any $a \geq 0$:

$$\sigma(2^a) = 1 + 2 + 4 + \cdots + 2^a = 2^{a+1} - 1.$$

Since $2^{a+1}$ is even, $2^{a+1} - 1$ is odd. Hence $\sigma(2^a)$ is odd for every $a \geq 0$.

### Step 2: For odd prime $p$, $\sigma(p^a)$ is odd iff $a$ is even

Let $p$ be an odd prime and $a \geq 1$. Consider

$$\sigma(p^a) = 1 + p + p^2 + \cdots + p^a.$$

Since $p$ is odd, every term $p^j$ is odd. This is a sum of $(a + 1)$ odd numbers.

A sum of $m$ odd numbers has parity equal to $m \bmod 2$: it is odd when $m$ is odd and even when $m$ is even. (Proof: each odd number is $\equiv 1 \pmod 2$, so the sum is $\equiv m \pmod 2$.)

Therefore:

$$\sigma(p^a) \text{ is odd} \iff (a + 1) \text{ is odd} \iff a \text{ is even}.$$

### Step 3: Combining via multiplicativity

Write $n = 2^{b} \cdot p_1^{a_1} \cdots p_r^{a_r}$ where $b \geq 0$ and $p_1 < p_2 < \cdots < p_r$ are odd primes. Then:

$$\sigma(n) = \sigma(2^b) \cdot \prod_{i=1}^{r} \sigma(p_i^{a_i}).$$

By Step 1, $\sigma(2^b)$ is always odd (regardless of $b$). By Step 2, each $\sigma(p_i^{a_i})$ is odd if and only if $a_i$ is even. Since the product of integers is odd iff every factor is odd:

$$\sigma(n) \text{ is odd} \iff \text{every } a_i \text{ is even } (i = 1, \ldots, r).$$

### Step 4: The odd part is a perfect square

The condition "every $a_i$ is even" means that in the prime factorization $n = 2^b \cdot p_1^{a_1} \cdots p_r^{a_r}$, each odd prime $p_i$ appears to an even power. This is precisely the condition that the **odd part** of $n$, namely

$$\text{odd}(n) = p_1^{a_1} \cdots p_r^{a_r},$$

is a perfect square (since a positive integer is a perfect square if and only if every prime in its factorization appears to an even power).

### Step 5: Equivalence with "square or twice a square"

We now show: $\text{odd}(n)$ is a perfect square if and only if $n$ is a perfect square or twice a perfect square.

Write $n = 2^b \cdot m^2$ where $m$ is odd and $m^2 = \text{odd}(n)$. Then:

- **If $b$ is even**, say $b = 2c$: then $n = 2^{2c} \cdot m^2 = (2^c \cdot m)^2$, which is a perfect square.
- **If $b$ is odd**, say $b = 2c + 1$: then $n = 2 \cdot 2^{2c} \cdot m^2 = 2 \cdot (2^c \cdot m)^2$, which is twice a perfect square.

Conversely:

- **If $n = k^2$** for some $k \geq 1$: write $k = 2^c \cdot d$ with $d$ odd. Then $n = 2^{2c} \cdot d^2$, so $\text{odd}(n) = d^2$ is a perfect square.
- **If $n = 2k^2$** for some $k \geq 1$: write $k = 2^c \cdot d$ with $d$ odd. Then $n = 2^{2c+1} \cdot d^2$, so $\text{odd}(n) = d^2$ is a perfect square.

### Conclusion

Combining Steps 3–5:

$$\boxed{\sigma(n) \text{ is odd} \iff n \text{ is a perfect square or twice a perfect square.}}$$

This holds for all $n \geq 1$. $\square$

## Remarks

1. **Small cases for verification:**
   - $\sigma(1) = 1$ (odd). $1 = 1^2$ ✓
   - $\sigma(2) = 3$ (odd). $2 = 2 \cdot 1^2$ ✓
   - $\sigma(3) = 4$ (even). $3$ is neither a square nor twice a square ✓
   - $\sigma(4) = 7$ (odd). $4 = 2^2$ ✓
   - $\sigma(5) = 6$ (even). $5$ is neither ✓
   - $\sigma(6) = 12$ (even). $6$ is neither ✓
   - $\sigma(7) = 8$ (even). $7$ is neither ✓
   - $\sigma(8) = 15$ (odd). $8 = 2 \cdot 4 = 2 \cdot 2^2$ ✓
   - $\sigma(9) = 13$ (odd). $9 = 3^2$ ✓
   - $\sigma(10) = 18$ (even). $10$ is neither ✓

2. **Application to iterated $\sigma$:** This characterization is essential for analyzing the parity dynamics of iterated sum-of-divisors. In particular, $\sigma(n)$ is even (and hence $n$ gains a factor of 2) whenever $n$ is not a square or twice a square — which is the "generic" case.

## References

- Multiplicativity of $\sigma$: standard result in elementary number theory.
- No external dependencies from the literature directory.
