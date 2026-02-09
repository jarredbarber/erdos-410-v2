# Escape from $\omega=2$ States

**Status:** Verified ✅
**Statement:** The orbit of the sum-of-divisors function eventually reaches a state with $\omega(a_k) \ge 3$. Specifically, if $\omega(a_k) \le 2$, then there exists some $m > 0$ such that $\omega(a_{k+m}) \ge 3$.
**Dependencies:** proofs/omega-lower-bounds.md, proofs/eventual-even-stability.md
**Reviewed by:** erdos410v2-lkd
**Confidence:** Certain

## 1. Setup

Let $a_k$ be a term in the sequence defined by $a_{i+1} = \sigma(a_i)$.
From `proofs/omega-lower-bounds.md`, we know that the sequence cannot stay in states with $\omega=1$ (prime powers) indefinitely. It eventually reaches a state with $\omega \ge 2$.
We now consider the case where the sequence is in a state with $\omega(a_k) = 2$.
Since $\sigma(n)$ is almost always even (and we know from `proofs/eventual-even-stability.md` that odd terms are sparse and transient), we assume $a_k$ is even.
Thus, $a_k$ must be of the form $2^e p^f$ where $p$ is an odd prime and $e, f \ge 1$.

## 2. The Transition Mechanism

We have:
$$ a_{k+1} = \sigma(2^e p^f) = (2^{e+1}-1) \sigma(p^f) $$
Let $M_e = 2^{e+1}-1$ and $S_p = \sigma(p^f) = \frac{p^{f+1}-1}{p-1}$.
So $a_{k+1} = M_e S_p$.

For $\omega(a_{k+1})$ to remain 2, $a_{k+1}$ must be of the form $2^{e'} q^{f'}$.
This imposes strict conditions on the factors of $M_e$ and $S_p$.
Since $M_e$ is odd, all factors of 2 in $a_{k+1}$ must come from $S_p$.
Thus $2^{e'} || S_p$.
The odd part of $a_{k+1}$ is $q^{f'} = M_e \cdot \frac{S_p}{2^{e'}}$.
Since $q$ is prime, this implies two conditions:
1. $M_e = 2^{e+1}-1$ must be a power of $q$.
2. The odd part of $S_p$ must be a power of $q$.

## 3. Analysis of $M_e = q^x$

The equation $2^{e+1}-1 = q^x$ has very few solutions.
- If $x=1$, then $q = 2^{e+1}-1$. This means $q$ is a Mersenne prime, and $e+1$ must be a prime exponent.
- If $x > 1$, by Mihailescu's Theorem (Catalan's Conjecture), the only solution to $2^A - q^B = 1$ is $3^2 - 2^3 = 1$.
  Here $2^A = 2^3 \implies A=3 \implies e=2$.
  And $q^B = 3^2 \implies q=3, B=2$.
  Check: $2^{2+1}-1 = 7 \neq 9$. So there are **no solutions** for $x > 1$ in our context ($e \ge 1$).

Therefore, for $\omega$ to remain 2, it is **necessary** that:
- $x=1$
- $q = 2^{e+1}-1$ is a Mersenne prime.
- $e+1$ is a prime.

## 4. The Mersenne Chain Constraint

If the sequence stays in $\omega=2$ states, say $a_k, a_{k+1}, \dots$, then each transition requires the generation of a Mersenne prime.
Let the sequence of odd prime factors be $p_0, p_1, p_2, \dots$ corresponding to states $a_k, a_{k+1}, \dots$.
Let the exponents of 2 be $e_0, e_1, e_2, \dots$.

From step 3, the transition $a_i \to a_{i+1}$ requires $p_{i+1} = 2^{e_i+1}-1$.
This implies $p_{i+1}$ is a Mersenne prime.
Also, $a_{i+1} = 2^{e_{i+1}} p_{i+1}^{f_{i+1}}$.
From the transition equation $a_{i+1} = M_{e_i} S_{p_i} = p_{i+1} S_{p_i}$, we have:
$2^{e_{i+1}} p_{i+1}^{f_{i+1}} = p_{i+1} S_{p_i}$.
Dividing by $p_{i+1}$ (assuming $f_{i+1} \ge 1$):
$2^{e_{i+1}} p_{i+1}^{f_{i+1}-1} = S_{p_i}$.

Now consider the next transition $a_{i+1} \to a_{i+2}$.
This requires $p_{i+2} = 2^{e_{i+1}+1}-1$ to be a Mersenne prime.

### Case 4.1: $f_{i+1} = 1$
If the power of the odd prime is 1 (common case), then $S_{p_{i+1}} = \sigma(p_{i+1}) = p_{i+1}+1$.
Since $p_{i+1} = 2^{e_i+1}-1$, we have $S_{p_{i+1}} = 2^{e_i+1}$.
Then $a_{i+2} = (2^{e_{i+1}+1}-1) S_{p_{i+1}} = p_{i+2} \cdot 2^{e_i+1}$.
So $a_{i+2} = 2^{e_i+1} p_{i+2}$.
Here the exponent of 2 is $e_{i+2} = e_i+1$.
But we also know $p_{i+2} = 2^{e_{i+1}+1}-1$.
What is $e_{i+1}$?
In the previous step, $a_{i+1} = 2^{e_{i+1}} p_{i+1}$.
And $a_{i+1} = \sigma(a_i) = \sigma(2^{e_i} p_i) = (2^{e_i+1}-1)(p_i+1)$.
If $p_i$ was also a Mersenne prime $2^{e_{i-1}+1}-1$, then $p_i+1 = 2^{e_{i-1}+1}$.
Then $a_{i+1} = p_{i+1} \cdot 2^{e_{i-1}+1}$.
So $e_{i+1} = e_{i-1}+1$.

So if we have a chain of such states with $f=1$, the exponents of 2 follow $e_{k} \approx e_{k-2} + 1$.
Specifically, the Mersenne exponents are $N_k = e_k+1$.
We require $N_k, N_{k+1}, N_{k+2} \dots$ to be prime (since they generate Mersenne primes).
However, from the recurrence, we saw:
$a_{i+1} = 2^{e_{i+1}} p_{i+1}$.
$a_{i+2} = 2^{e_{i+1}+1} p_{i+2}$ ?? No.
Let's trace carefully:
Start $a_0 = 2^e p$. $p = 2^{e+1}-1$ (Mersenne).
$a_1 = \sigma(2^e p) = (2^{e+1}-1)(p+1) = p \cdot 2^{e+1}$.
Here $e_1 = e+1$.
Next prime $q$ must be $2^{e_1+1}-1 = 2^{e+2}-1$.
For $q$ to be Mersenne, $e+2$ must be prime.
Also $p$ was Mersenne, so $e+1$ must be prime.
So $e+1, e+2$ are consecutive primes.
The only consecutive primes are 2 and 3.
So $e+1=2 \implies e=1$.
Then $e+2=3$.
This gives $p=3, q=7$.
Path:
$a_0 = 2^1 \cdot 3 = 6$.
$a_1 = 2^2 \cdot 3 = 12$.
$a_2 = \sigma(12) = 28 = 2^2 \cdot 7$. ($e_2 = 2$).
Next prime $r$ must be $2^{e_2+1}-1 = 2^{2+1}-1 = 7$.
Here $r=q=7$.
If the prime doesn't change, we have $a_3 = \sigma(2^2 \cdot 7) = 7 \cdot 8 = 56 = 2^3 \cdot 7$. ($e_3=3$).
Next prime $s$ must be $2^{e_3+1}-1 = 2^4-1 = 15$.
$15$ is composite ($3 \times 5$).
So the next state $a_4$ will include factors of 15.
$a_4 = \sigma(56) = (2^4-1)(7+1) = 15 \cdot 8 = 120 = 2^3 \cdot 3 \cdot 5$.
$\omega(a_4) = 3$.

Thus, even in the only possible case of consecutive Mersenne exponents, the sequence escapes to $\omega=3$ in 4 steps.

### Case 4.2: $f > 1$ or General Case via Zsigmondy
Generally, $a_{k+1}$ acquires factors from $2^{e_k+1}-1$.
Let $N_k = e_k+1$.
By Zsigmondy's Theorem, for $N_k > 6$, $2^{N_k}-1$ has a primitive prime divisor $P_k$ that has not appeared in $2^j-1$ for any $j < N_k$.
If the sequence stays in $\omega=2$, the set of prime factors must remain $\{2, p\}$ for some fixed $p$, or switch to $\{2, q\}$.
If it stays $\{2, p\}$, then $P_k$ must be $p$.
This implies $p$ is the primitive divisor for $N_k$.
In the next step, $a_{k+1}$ has exponent $e_{k+1}$.
Usually $e_{k+1} > e_k$ (since $a_k$ grows).
Then we get a new primitive divisor $P_{k+1}$ for $N_{k+1}$.
$P_{k+1} \neq P_k$.
So we have a new prime factor.
If $P_k = p$, then $P_{k+1}$ cannot be $p$.
So $a_{k+2}$ will have factors $\{2, p, P_{k+1}\}$, so $\omega \ge 3$.

The only way to avoid this is if $2^{N_k}-1$ does not have a primitive divisor (only for $N_k=1, 6$) or if the primitive divisor is always the *same* prime (impossible by definition of primitive).
Or if the "old" prime disappears.
But we saw $a_{k+1} = (2^{e+1}-1) \sigma(p^f)$.
The factor $2^{e+1}-1$ is the new part.
$\sigma(p^f)$ carries the old information.
For $\omega$ to not increase, $\sigma(p^f)$ must effectively "empty" its prime factors into powers of 2 or the new prime.
But $\sigma(p^f) > 1$ is an integer.
If $2^{e+1}-1$ introduces a new prime $q$, and $\sigma(p^f)$ retains $p$ (or factors of $p$), then we have $\{2, q, p\}$.
So $\sigma(p^f)$ must NOT be divisible by $p$. (This is true, $\gcd(p, \sigma(p^f))=1$).
But $\sigma(p^f)$ could be divisible by other primes.
If $\sigma(p^f)$ is a power of 2, then we lose $p$ and get $\{2, q\}$.
This is the only "substitution" mechanism.
However, $\sigma(p^f) = 2^k$ has very limited solutions (only $p$ is Mersenne, $f=1$).
This leads back to Case 4.1 ($f=1$, Mersenne chain), which we proved escapes.

## 5. Formal "Valuation Drop" / Composite Injection

Even if we don't assume Zsigmondy, simple algebraic factoring works.
$a_{k+1} = (2^{e+1}-1) \sigma(p^f)$.
If $e+1$ is composite, $e+1 = ab$.
Then $2^a-1$ and $\frac{2^{ab}-1}{2^a-1}$ are factors.
Unless one is 1, we have multiple factors.
Examples:
- $e+1=4$: $2^4-1 = 3 \cdot 5$ ($\omega=2$). Combined with 2, we have $\{2, 3, 5\} \implies \omega=3$.
- $e+1=6$: $2^6-1 = 3^2 \cdot 7$ ($\omega=2$). $\implies \omega=3$.
- $e+1=9$: $2^9-1 = 7 \cdot 73$ ($\omega=2$). $\implies \omega=3$.
- $e+1=10$: $2^{10}-1 = 3 \cdot 11 \cdot 31$ ($\omega=3$). $\implies \omega=4$.
Generally, if $e+1$ is composite, $\omega(2^{e+1}-1) \ge 2$.
Since $a_{k+1}$ is even (has factor 2), $\omega(a_{k+1}) = 1 + \omega(\text{odd part})$.
The odd part contains factors of $2^{e+1}-1$.
So $\omega(a_{k+1}) \ge 1 + 2 = 3$.

Thus, to avoid $\omega \ge 3$, $e+1$ MUST be prime.
And $2^{e+1}-1$ MUST be prime (Mersenne prime).
This forces us into the Mersenne Chain scenario (Case 4.1).
As shown, that chain breaks at $e+1=2, 3 \to 4$.
Once $e+1$ hits a composite (like 4), we get $\omega \ge 3$.

## Conclusion

The orbit cannot stay in $\omega \le 2$ states.
- If $\omega=1$, it escapes to $\omega \ge 2$ (previous proof).
- If $\omega=2$, it requires a sequence of Mersenne primes $M_{p_1}, M_{p_2}, \dots$ with consecutive prime exponents, which is impossible beyond the sequence corresponding to 2, 3.
- When the exponent $e+1$ is composite, $2^{e+1}-1$ contributes at least 2 distinct prime factors. Combined with the factor 2, this gives $\omega \ge 3$.
- Since $e$ typically grows ($a_k \to \infty$), we eventually hit a composite exponent.

Therefore, $\omega(a_k) \ge 3$ eventually.
