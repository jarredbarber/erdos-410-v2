# Lower Bounds on $\omega(2^n-1)$ and Mersenne Instability

**Status:** Verified ✅
**Reviewed by:** erdos410v2-emu
**Statement:** For all $n \ge 1$, $\omega(2^n-1) \ge \tau(n) - 2$. Furthermore, the orbit cannot get stuck in a cycle of Mersenne primes; any "Mersenne form" $a_k = 2^p-1$ (where $p$ is prime) leads to a value $a_{k+m}$ with $\omega \ge 2$ within at most 4 steps ($m \le 4$).

## 1. Lower Bound on $\omega(2^n-1)$

We claim that the number of distinct prime factors of $2^n-1$ is bounded below by the number of divisors of $n$, with a small constant correction.

**Theorem:** For all $n \ge 1$, $\omega(2^n-1) \ge \tau(n) - 2$.

**Proof:**
Let $d$ be a divisor of $n$. Then $2^d-1$ divides $2^n-1$.
By Zsigmondy's Theorem, for any $d > 1$ except $d=6$, the number $2^d-1$ has a primitive prime divisor $p_d$ — a prime that divides $2^d-1$ but does not divide $2^k-1$ for any $k < d$.

Primitive prime divisors for distinct $d$ are distinct.
- If $p_a$ is primitive for $2^a-1$ and $p_b$ is primitive for $2^b-1$ with $a \neq b$, then $p_a \neq p_b$ because $ord_{p_a}(2) = a$ and $ord_{p_b}(2) = b$.

Thus, for every divisor $d|n$ such that $d \neq 1$ and $d \neq 6$, there is at least one unique prime factor $p_d$ of $2^n-1$.
The number of such divisors is $\tau(n) - 1$ (excluding $d=1$) if $6 \nmid n$, or $\tau(n) - 2$ (excluding $d=1$ and $d=6$) if $6 | n$.
In either case, the count of distinct prime factors is at least $\tau(n) - 2$.
Therefore, $\omega(2^n-1) \ge \tau(n) - 2$.

**Examples:**
- $n=12$: Divisors $\{1, 2, 3, 4, 6, 12\}$. Primitive divisors exist for $2, 3, 4, 12$. ($d=6$ is exceptional). Count $\ge 6-2=4$. Actual $\omega(4095) = \omega(3 \cdot 5 \cdot 7 \cdot 13) = 4$. (Bound is tight).
- $n=p$ (prime, $p \neq 6$): Divisors $\{1, p\}$. Primitive for $p$. Count $\ge 2-1=1$. (Consistent with Mersenne primes).

## 2. Mersenne Instability

A potential "weakness" of the Factor Pump is if the sequence gets stuck in states with $\omega=1$. We show that if the sequence hits a Mersenne prime, it must eventually escape to a state with $\omega \ge 2$.

We assume the standard recurrence $a_{k+1} = \sigma(a_k)$.

**Claim:** If $a_k = 2^p-1$ is a Mersenne prime, then there exists $m \le 4$ such that $\omega(a_{k+m}) \ge 2$. Specifically, $m=2$ for $p > 2$, and $m=4$ for $p=2$.

**Proof:**
1. Assume $a_k = M_p = 2^p-1$ is a Mersenne prime.
2. $\sigma(a_k) = \sigma(2^p-1) = 1 + (2^p-1) = 2^p$.
3. Thus $a_{k+1} = 2^p$. Since $p$ is prime, $\omega(a_{k+1}) = 1$.
4. $\sigma(a_{k+1}) = \sigma(2^p) = 2^{p+1}-1$.
5. Thus $a_{k+2} = 2^{p+1}-1$.

We analyze the prime factorization of $a_{k+2}$ based on $p$.

**Case 1: $p > 2$**
Since $p$ is a prime greater than 2, $p$ is odd.
Therefore, $p+1$ is even and greater than 3.
This implies $p+1$ is composite.
Consequently, $a_{k+2} = 2^{p+1}-1$ is composite.
By Mihailescu's Theorem (Catalan's Conjecture), $2^{p+1}-1$ is not a perfect power for $p+1 > 1$. Specifically, the equation $2^{p+1} - q^k = 1$ has no solutions in integers $p, q, k > 1$ (the only solution to $x^a - y^b = 1$ is $3^2 - 2^3 = 1$, but here the base of the positive term is 2, not 3).
Thus, $a_{k+2}$ is not a prime power.
Since it is composite and not a prime power, it must have at least two distinct prime factors.
So $\omega(a_{k+2}) \ge 2$.
In this case, the escape happens at $m=2$.

**Case 2: $p = 2$**
$a_k = 2^2-1 = 3$.
$a_{k+1} = 2^2 = 4$.
$a_{k+2} = 2^3-1 = 7$.
Here $a_{k+2}$ is prime (Mersenne prime $M_3$), so $\omega(a_{k+2}) = 1$.
We continue the iteration:
$\sigma(a_{k+2}) = \sigma(7) = 8$.
$a_{k+3} = 8 = 2^3$.
$\omega(a_{k+3}) = 1$.
$\sigma(a_{k+3}) = \sigma(2^3) = 2^4-1 = 15$.
$a_{k+4} = 15 = 3 \cdot 5$.
$\omega(a_{k+4}) = 2$.
In this case, the escape happens at $m=4$.

**Conclusion:** The sequence can spend at most 4 steps in states with $\omega=1$ (specifically the chain $3 \to 4 \to 7 \to 8 \to 15$) before hitting a state with $\omega \ge 2$. For all other Mersenne primes, it takes only 2 steps.

## 3. Asymptotic Strength (Heuristic)

As $\omega(a_k)$ grows, $v_2(a_{k+1}) \approx \omega(a_k)$ grows.
Let $N = v_2(a_{k+1}) + 1$.
The density of primes (and thus Mersenne exponents) near $N$ is $1/\ln N$.
The probability that $N$ is a Mersenne exponent vanishes as $N \to \infty$.
Therefore, for large $k$, the Factor Pump almost always uses a composite $N$, ensuring $\omega(a_{k+2}) \ge \tau(N) - 2$.
Since $N$ is likely highly composite (or at least not prime), $\tau(N)$ provides a significant boost to $\omega$.

## References
- Zsigmondy's Theorem
- Mihailescu's Theorem (Catalan's Conjecture)
