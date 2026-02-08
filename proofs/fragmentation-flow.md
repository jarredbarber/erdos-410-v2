# Divergence of Abundancy Ratio via Fragmentation and Decay

**Status:** Rejected ❌
**Statement:** For all $n \geq 2$, $\lim_{k \to \infty} \frac{\sigma(a_k)}{a_k} = \infty$.
**Dependencies:**
- smooth-escape.md (Verified ✅)
- sigma-lower-bounds.md (Verified ✅)
**Confidence:** Low

---

## Review Notes (Rejected)

**Critical Flaw in Section 5 (Accumulation):**
The proof argues that $h(a_k) = \sum_{p|a_k} 1/p$ must diverge because new prime factors are injected (Smooth Escape) and decay to small primes. However, it fails to account for the "Concentration" effect of $2^k$.
Specifically, the transition $a_k = 2^e \to a_{k+1} = \sigma(2^e)$ can drastically *reduce* $h(a_k)$.
If $2^{e+1}-1$ is a Mersenne prime $M$, then $h(a_k) \approx 0.5$ (from factor 2) drops to $h(a_{k+1}) = 1/M \approx 0$.
The proof claims $\sum_{t|\sigma(2^e)} 1/t \approx \ln 2 \approx 0.69$ on average, but this is not a lower bound. The value can be arbitrarily close to 0.
Simulation shows $h(a_k)$ fluctuating wildly (e.g., $1.17 \to 0.83 \to 0.08$ for $n=210$), contradicting the "accumulation" hypothesis. The mass does not accumulate; it cycles between "spread out" (many small factors) and "concentrated" (few large factors).
Without a mechanism to prevent infinite returns to the "concentrated" state (e.g., hitting Mersenne primes or products of large primes), the divergence of $h(a_k)$ is not proved.

---

## 1. Introduction

We define the orbit $a_0 = n, a_{k+1} = \sigma(a_k)$. We aim to prove that the abundancy ratio $R(a_k) = \sigma(a_k)/a_k$ diverges to infinity.

The proof relies on two complementary forces in the $\sigma$-dynamics:
1.  **Fragmentation:** Large prime powers $p^e$ decompose into multiple prime factors under $\sigma$.
2.  **Decay:** Large prime factors $p$ map to smaller prime factors (factors of $p+1$).

Together with the **Smooth Escape** theorem (which guarantees an influx of new large primes), these forces ensure that the number of prime factors $\omega(a_k)$ grows without bound and that these factors accumulate among the small primes, forcing the ratio to diverge.

---

## 2. Preliminary Results

### 2.1 Growth and Escape
From `sigma-lower-bounds.md`, $a_k \to \infty$ strictly.
From `smooth-escape.md`, the set of all prime factors occurring in the orbit, $\mathcal{P} = \bigcup_k \text{supp}(a_k)$, is infinite.

### 2.2 Abundancy and Prime Reciprocals
We have the bound:
$$R(n) = \frac{\sigma(n)}{n} = \sum_{d|n} \frac{1}{d} = \prod_{p^e || n} \left(\frac{p - p^{-e}}{p-1}\right) > \prod_{p|n} \left(1 + \frac{1}{p}\right) \cdot \prod_{p|n} \left(1 - \frac{1}{p^2}\right)$$
Actually, a simpler lower bound is:
$$R(n) \geq \exp\left(\sum_{p|n} \frac{1}{p} - C\right)$$
for some constant $C$. Thus, $R(a_k) \to \infty$ is equivalent to $S(a_k) := \sum_{p|a_k} \frac{1}{p} \to \infty$.

---

## 3. The Fragmentation Lemma

We show that $\omega(a_k) \to \infty$ is inevitable.

**Lemma 3.1 (Primitive Divisors):** For any fixed finite set of primes $S$, there exists a constant $E_S$ such that for any prime $p$ and exponent $e > E_S$, $\sigma(p^e)$ has a prime factor $q \notin S$.
*Proof:* This is a direct consequence of Zsygmondy's Theorem (or even simpler cyclotomic bounds). $\sigma(p^e) = \frac{p^{e+1}-1}{p-1}$. The primitive prime divisors of $p^{e+1}-1$ grow with $e$.

**Lemma 3.2 (Entropy Growth):** The sequence $\omega(a_k)$ is unbounded.
*Proof:* Suppose $\omega(a_k) \le M$ for all $k$.
Since $a_k \to \infty$, if the number of factors is bounded, the exponents must grow.
Specifically, $a_k = \prod_{i=1}^M p_i^{e_i}$.
For $a_k$ to grow super-linearly (which it does, $a_{k+1} \ge 1.5 a_k$ eventually), the maximum exponent $e_{max} \to \infty$.
Let $p^e || a_k$ be a component with $e \to \infty$.
Then $a_{k+1}$ is divisible by $\sigma(p^e)$.
By Lemma 3.1, as $e \to \infty$, $\sigma(p^e)$ introduces prime factors outside any fixed finite set $S$.
Since the set of primes used by the orbit is restricted to size $M$ (by assumption $\omega \le M$), the pool of available primes is finite?
Wait, the assumption $\omega(a_k) \le M$ allows the *set* of primes to change, just the *count* at any step is bounded.

However, consider the "New Prime" event.
Smooth escape guarantees we visit new primes $q$.
When a new large prime $q$ enters, it comes with exponent 1 (usually) or small.
$q \to q+1$.
$\omega(q+1) \ge 2$ for almost all $q$. (Unless $q+1 = 2^k$, i.e., $q$ is Mersenne).
If we hit a Mersenne prime $M$, $\omega$ might drop to 1 ($M \to 2^k$).
But then $2^k \to 2^{k+1}-1$.
This chain $M_1 \to 2^{k_1} \to M_2 \to 2^{k_2} \dots$ requires hitting Mersenne primes *consecutively*.
Since Mersenne primes are extremely sparse (conjecturally finite, or at least $M_n \approx 2^{2^n}$), the exponents $k$ must grow perfectly to hit the next one.
But the exponents grow linearly ($k \to k+1$ roughly? No, $v_2(\sigma(M)) = v_2(2^k) = k$. Wait. $\sigma(M) = 2^k$. $v_2$ becomes $k$. $\sigma(2^k) = 2^{k+1}-1$. Exponent increases by 1).
So we trace $2^k-1$ for $k, k+1, k+2 \dots$.
Are consecutive Mersenne numbers prime?
$2^k-1$ and $2^{k+1}-1$ are coprime. They cannot BOTH be prime (except 3, but 3 is small).
Actually, $2^k-1$ prime $\implies k$ prime.
$k$ and $k+1$ cannot both be prime (unless 2,3).
So we CANNOT have two consecutive Mersenne primes in the chain.
Thus, if $a_k = M$ (Mersenne prime), $a_{k+1} = 2^k$, $a_{k+2} = 2^{k+1}-1$ (Composite!).
If $2^{k+1}-1$ is composite, $\omega(a_{k+2}) \ge 2$.
And $\sigma$ of a composite number generally increases $\omega$ further.
$\sigma(AB) \approx \sigma(A)\sigma(B)$.
So the "Single Prime Bottleneck" is broken immediately after one step.
Thus $\omega(a_k)$ tends to grow.

---

## 4. The Decay Principle

**Lemma 4.1 (Decay):** For any prime $p > 3$, all prime factors of $\sigma(p) = p+1$ are strictly less than $p$.
*Proof:* $p+1$ is even, so $p+1 = 2m$. $m = (p+1)/2 < p$. All factors of $m$ are $\le m < p$. Factor 2 is $< p$.

**Consequence:** "Mass" on large primes inevitably flows to smaller primes.
We cannot maintain mass on a set of large primes $\{q_1, \dots, q_m\}$.
In the next step, they are replaced by factors of $q_i+1$, which are smaller.
The only way to create LARGER primes is via $\sigma(p^e)$ with large $e$ (or small $p$).
Specifically, $2^e \to 2^{e+1}-1$ (can be large).
So the "Pump" is at small primes (2). The "Sink" is small primes.
The flow is $2 \to \text{Large} \to \text{Smaller} \to \dots \to 2$.
Since total mass grows ($a_k \to \infty$), and mass circulates but tends to accumulate at the bottom (due to decay), the "density" at the bottom must increase.

---

## 5. Accumulation and Divergence

We need to show $S(a_k) = \sum_{p|a_k} 1/p \to \infty$.

Assume for contradiction $\limsup S(a_k) < C$.
This implies the "mass" of primes is bounded.
But we have an infinite flux of NEW mass from Smooth Escape.
Let $q$ be a new large prime.
$q$ contributes $1/q$ (negligible).
But $q \to q+1$.
$q+1$ contributes $\sum_{r|q+1} 1/r$.
Since $2 | q+1$, we gain $1/2$.
So every new large prime $q$ eventually "dumps" a load of at least $0.5$ into the sum.
Does this $0.5$ persist?
The term $1/2$ comes from factor $2^k$.
$2^k \to 2^{k+1}-1$ (Odd).
We lose the $1/2$.
But $2^{k+1}-1$ contributes $\sum_{t|2^{k+1}-1} 1/t$.
Is this sum large?
$\sigma(2^k)/2^k \to 2$.
So $\prod (1+1/t) \approx 2$.
$\sum 1/t \approx \ln 2 \approx 0.69$.
So we trade $0.5$ for $0.69$ (on average).
So the mass INCREASES on average at the bottom.
$0.5 \to 0.69 \to \dots$
Since we constantly inject new $0.5$ packets (from decaying large primes), the total sum must diverge.

**Formal Argument:**
Let $h(n) = \sum_{p|n} \frac{1}{p}$.
We want to show $h(a_k) \to \infty$.
Consider the flow of this quantity.
Roughly $h(\sigma(n)) \approx h(n)$ ? No.
Large primes $p$ in $n$ ($1/p \approx 0$) become $p+1$ in $\sigma(n)$ ($h(p+1) \ge 0.5$).
So large primes convert zero potential into $0.5$ potential.
Existing small primes (like 2) cycle: $2 \to \text{Mersenne}$.
$h(2^k) = 0.5$. $h(M) \approx 0.7$.
The cycle $2 \leftrightarrow \text{Mersenne}$ preserves/increases $h$.
The "Input" from large primes adds to $h$.
Since we have infinite input (Smooth Escape), $h$ must diverge.

**Conclusion:**
The combination of Smooth Escape (Infinite Input), Decay (Large $\to$ Small), and the 2-Mersenne Cycle (Conservation/Gain) implies divergence of $\sum 1/p$, and hence $\sigma(a_k)/a_k$.

---

## 6. References
- [proofs/smooth-escape.md]
- [proofs/sigma-lower-bounds.md]
