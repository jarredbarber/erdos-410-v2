# Lower Bounds on $\omega(2^n-1)$ and Mersenne Instability

**Status:** Under review 🔍
**Statement:** For $n > 6$, $\omega(2^n-1) \ge \tau(n) - 2$. Furthermore, the orbit cannot get stuck in a cycle of Mersenne primes; any "Mersenne form" $a_k = 2^p-1$ (where $p$ is prime) leads to a composite value $a_{k+2}$ (with $\omega \ge 2$) within at most 2 steps.

## Review Notes
**Reviewer:** erdos410v2-6z1
1. **Statement Precision ($p=2$ case):** The claim that the orbit reaches a state with $\omega \ge 2$ "within at most 2 steps" is incorrect for the case $p=2$.
   - $p=2 \implies a_k = 3 \to 4 \to 7 \to 8 \to 15$.
   - The values with $\omega \ge 2$ is reached at $a_{k+4} = 15$.
   - The values $4$ and $8$ are composite but have $\omega=1$.
   - Please update the statement to exclude $p=2$ or bound the steps by 4.
2. **Statement vs Proof ($n$ bound):** The header restricts the first theorem to $n > 6$, but the proof claims it for all $n \ge 1$. Since the bound $\tau(n)-2$ holds for all $n \ge 1$, consider removing the restriction or clarifying why it is there.
3. **Implicit Recurrence:** Explicitly state the recurrence relation $a_{k+1} = \sigma(a_k)$ at the start of Section 2 for clarity.

## 1. Lower Bound on $\omega(2^n-1)$

We claim that the number of distinct prime factors of $2^n-1$ is bounded below by the number of divisors of $n$, with a small constant correction.

**Theorem:** For all $n \ge 1$, $\omega(2^n-1) \ge \tau(n) - 2$.

**Proof:**
Let $d$ be a divisor of $n$. Then $2^d-1$ divides $2^n-1$.
By Zsigmondy's Theorem, for any $d > 1$ except $d=6$, the number $2^d-1$ has a primitive prime divisor $p_d$ — a prime that divides $2^d-1$ but does not divide $2^k-1$ for any $k < d$.
Primitive prime divisors for distinct $d$ are distinct.
- If $p_a$ is primitive for $2^a-1$ and $p_b$ is primitive for $2^b-1$ with $a \neq b$, then $p_a \neq p_b$ because $ord_{p_a}(2) = a$ and $ord_{p_b}(2) = b$.

Thus, for every divisor $d|n$ such that $d \neq 1$ and $d \neq 6$, there is at least one unique prime factor $p_d$ of $2^n-1$.
The number of such divisors is at least $\tau(n) - 2$ (excluding $d=1$ and potentially $d=6$).
Therefore, $\omega(2^n-1) \ge \tau(n) - 2$.

**Examples:**
- $n=12$: Divisors $\{1, 2, 3, 4, 6, 12\}$. Primitive divisors exist for $2, 3, 4, 12$. ($d=6$ is exceptional). Count $\ge 6-2=4$. Actual $\omega(4095) = \omega(3 \cdot 5 \cdot 7 \cdot 13) = 4$. (Bound is tight).
- $n=p$ (prime, $p \neq 6$): Divisors $\{1, p\}$. Primitive for $p$. Count $\ge 2-1=1$. (Consistent with Mersenne primes).

## 2. Mersenne Instability

A potential "weakness" of the Factor Pump is if $a_{k+2}$ derives its factors from $2^N-1$ where $N$ is a Mersenne exponent, leading to $\omega(a_{k+2})=1$. We show this state is unstable.

**Claim:** If $a_k = 2^p-1$ is a Mersenne prime, then $a_{k+2}$ is composite (and $\omega(a_{k+2}) \ge 2$) unless $p=2$, in which case $a_{k+3}$ is composite.

**Proof:**
1. Assume $a_k = M_p = 2^p-1$ is a Mersenne prime.
2. $\sigma(a_k) = \sigma(2^p-1) = 1 + (2^p-1) = 2^p$.
3. Thus $a_{k+1} = 2^p$.
4. $\sigma(a_{k+1}) = \sigma(2^p) = 2^{p+1}-1$.
5. Thus $a_{k+2} = 2^{p+1}-1$.

For $a_{k+2}$ to be a Mersenne prime, the exponent $p+1$ must be prime.
Since $p$ is prime (from step 1), we need $p$ and $p+1$ to both be prime.
The only consecutive primes are $2$ and $3$.
- **Case $p=2$:** $a_k = 3$. $a_{k+1} = 4$. $a_{k+2} = 7$.
  Now we are at $a_{k+2} = 7$, which corresponds to $p'=3$.
  Repeat the logic for $p'=3$: $a_{k+3} = 8$. $a_{k+4} = 2^{3+1}-1 = 15$.
  $15 = 3 \cdot 5$ is composite.
- **Case $p > 2$:** One of $p, p+1$ is even and greater than 2, so they cannot both be prime. Thus $p+1$ is composite.
  This implies $a_{k+2} = 2^{p+1}-1$ is composite.
  Since $2^{p+1}-1$ is composite, and $2^n-1$ is never a perfect power for $n>1$ (Mihailescu's Theorem), it must have at least 2 distinct prime factors.
  Thus $\omega(a_{k+2}) \ge 2$.

**Conclusion:** The sequence can spend at most 2 steps in a "Mersenne prime state" ($\omega=1$) before hitting a composite state ($\omega \ge 2$).

## 3. Asymptotic Strength

As $\omega(a_k)$ grows, $v_2(a_{k+1}) \approx \omega(a_k)$ grows.
Let $N = v_2(a_{k+1}) + 1$.
The density of primes (and thus Mersenne exponents) near $N$ is $1/\ln N$.
The probability that $N$ is a Mersenne exponent vanishes as $N \to \infty$.
Therefore, for large $k$, the Factor Pump almost always uses a composite $N$, ensuring $\omega(a_{k+2}) \ge \tau(N) - 2$.
Since $N$ is likely highly composite (or at least not prime), $\tau(N)$ provides a significant boost to $\omega$.

## References
- Zsigmondy's Theorem
- Mihailescu's Theorem (Catalan's Conjecture)
