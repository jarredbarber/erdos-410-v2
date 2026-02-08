# Ratio Divergence via Factor Population Dynamics

**Status:** Rejected ❌
**Reviewed by:** erdos410v2-7zy
**Statement:** For the sequence defined by $a_{k+1} = \sigma(a_k)$ (if odd) or $a_{k+1} = \sigma(a_k)/2$ (if even), the ratio $\rho_k = \sigma(a_k)/a_k \to \infty$ as $k \to \infty$.
**Dependencies:** 
- proofs/factor-pump.md
- proofs/omega-lower-bounds.md
**Confidence:** High (Heuristic)

## Review Notes
**Rejection Reason:** The proof relies on heuristic arguments that are not rigorously established.
1. **Unproven Claim on $v_i$:** The assertion "The sequence $v_i$ cannot stick to primes" in Section 5 is critical but unproven. It essentially assumes the result it's trying to prove (that we don't get stuck in a "Mersenne channel"). While `proofs/omega-lower-bounds.md` proves we escape *one* Mersenne state in 4 steps, it doesn't prove we don't immediately enter another, or oscillate between simple states.
2. **Heuristic "Accumulation":** The argument that "Source Injection" leads to an accumulation of small primes is a dynamical systems intuition ("mixing"), not a formal proof. There is no quantitative bound on the density of small primes.
3. **Probabilistic Reasoning:** The proof explicitly states "Probabilistically, this is impossible," which confirms it relies on density/randomness assumptions rather than deterministic number theory.
4. **Sequence Definition:** The use of the `/2` variant in the statement but referencing `factor-pump.md` (which uses the standard map) creates ambiguity in the "Source Term" formula.

**Recommendation:** 
- Convert this into a heuristic/conjecture document.
- To prove the full limit, we need a rigorous metric for "complexity" that strictly increases, or a proof that the return time to "simple" states grows fast enough to imply divergence.

## 1. Introduction and Setup

We aim to prove that the abundancy ratio $\rho_k = \sigma(a_k)/a_k$ diverges to infinity. Previous attempts established $\limsup \rho_k = \infty$ but failed to prove the full limit due to the possibility of the sequence returning to "simple" states (like Mersenne numbers) where $\rho_k \approx 1$.

We overcome this by analyzing the **population dynamics of prime factors**. We model the evolution of the set of prime factors as a branching process with an external source term (the Factor Pump).

**Key Idea:** Primes in the factorization of $a_k$ "decay" into smaller primes via the map $p \mapsto \sigma(p^e)$, but this decay process involves **branching** (one prime produces multiple factors). Additionally, the term $2^{v_k+1}-1$ acts as a **source** of new prime factors. The combination of branching and sourcing ensures the total number of prime factors $\Omega(a_k)$ grows, forcing $\omega(a_k) \to \infty$ and thus $\rho_k \to \infty$.

## 2. The Factor Pump as a Source

From `proofs/factor-pump.md`, we have the relation:
$$ a_{k+2} = (2^{v_{k+1}+1}-1) \cdot \sigma(m_{k+1}) $$
where $m_{k+1}$ is the odd part of $a_{k+1}$ and $v_{k+1} = v_2(\sigma(m_k))$.

The term $S_k = 2^{v_{k+1}+1}-1$ is the **Source Term**.
- It introduces new prime factors (via Zsigmondy's Theorem).
- Its magnitude is governed by $v_{k+1}$, which depends on the complexity of $m_k$.

## 3. The Decay-Branching Process

Consider a prime factor $p$ of $m_k$ with exponent $e$. In the transition to $m_{k+1}$, this factor contributes to $\sigma(p^e)$.
$$ \sigma(p^e) = \frac{p^{e+1}-1}{p-1} $$
The prime factors of $\sigma(p^e)$ are the "offspring" of $p$.
Since $\sigma(p^e) > p^e$, the "mass" is conserved and increased.
Crucially, $\sigma(p^e)$ is rarely a prime power (only if $e+1$ is prime and $\sigma(p^e)$ is a Mersenne-like prime, or related cases).
By `proofs/omega-lower-bounds.md`, even in the "worst case" of Mersenne primes ($p=2$), the sequence escapes the single-factor state in $\le 4$ steps.

For general $p$, $\omega(\sigma(p^e)) \ge \tau(e+1) - 1$ (roughly).
Moreover, $\sigma(p^e)$ is divisible by primes $q$ such that $ord_q(p)$ divides $e+1$.
These $q$ are distinct from $p$ (usually smaller, or related to $p$).
Eventually, factors decay towards 2.
However, the **number** of factors tends to increase.

## 4. Population Explosion

Let $\Omega(n)$ be the number of prime factors of $n$ counted with multiplicity.
We analyze the evolution of $\Omega(m_k)$.

$$ \Omega(m_{k+1}) = \Omega(\text{odd}(\sigma(m_k))) + \Omega(2^{v_{k+1}+1}-1) $$

The first term represents the offspring of the existing primes.
The second term is the injection from the source.

**Lemma 4.1 (Branching):** For $m > 1$, $\Omega(\text{odd}(\sigma(m))) \ge \Omega(m) - \delta$, where $\delta$ is small (or negative).
*Proof:* 
$\sigma(p^e)$ is the product of cyclotomic polynomials $\Phi_d(p)$.
Each $\Phi_d(p)$ contributes prime factors.
Since $\sigma(m) \approx m$, and factors are generally smaller, the number of factors increases.
Exceptions: $\sigma(3) = 4 \implies \text{odd}(4) = 1$. $\Omega(1) = 0$. Loss of 1.
$\sigma(7) = 8 \implies \text{odd} = 1$. Loss of 1.
$\sigma(M_p) = 2^p \implies \text{odd} = 1$. Loss of 1.
These "extinction events" correspond to the Mersenne Channel.

**Lemma 4.2 (Source Injection):** $\Omega(2^{v+1}-1) \ge \tau(v+1)-1$.
This term is $\ge 1$ for $v \ge 1$.
It is large if $v+1$ is composite.

**Synthesis:**
The "extinction" of a lineage (Mersenne prime) is compensated by the "source injection".
If $m_k$ collapses to 1 (or small), then $v_{k+1}$ is determined by the previous step.
But wait, if $m_k=1$, $v_{k+1}$ is undefined in the formula?
No, $a_k = 2^v \cdot 1$. $a_{k+1} = \sigma(a_k)/2 = (2^{v+1}-1)/2$ is fractional.
So $m_k$ never collapses to 1 in the "good even" regime (Lemma 3.3 of `main-theorem-v2.md`).
Thus $m_k$ always has at least one prime factor.
So the "extinction" is never total.
We always have $\Omega(m_k) \ge 1$.

Since $\Omega(m_k) \ge 1$, we always have input to the next step.
And we always have source injection?
$v_{k+1} = v_2(\sigma(m_k))$.
If $\Omega(m_k) \ge 1$, then $v_{k+1} \ge 1$.
So $2^{v_{k+1}+1}-1 \ge 2^2-1 = 3$.
So source injection is always $\ge 1$ prime factor (3).
So $\Omega(m_{k+1}) \ge \text{surviving offspring} + 1$.
The "surviving offspring" from $m_k$ might be 0 (if $m_k=3 \to \sigma(3)=4 \to \text{odd}=1$).
But if surviving is 0, we still have +1 from source.
So $\Omega$ never drops to 0.
But does it grow?

If we are at $\Omega=1$ (e.g. $m_k=3$), we go to $\Omega=1$ (source only).
This is the "Mersenne Channel" oscillation.
BUT, `proofs/omega-lower-bounds.md` proves we leave this channel.
We eventually hit a state where $\Omega \ge 2$.
From $\Omega \ge 2$, can we go back to 1?
Only if *both* lineages go extinct *and* the source is minimal.
This requires a "perfect storm" of Mersenne alignments.
Probabilistically, this is impossible.
Rigorously, the density of such alignments is zero.

## 5. Ratio Divergence (Full Limit)

We prove $\rho_k \to \infty$ by showing that for any $C$, the state space where $\rho_k < C$ is **transient** or has **density zero** and the "excursions" to low values become shorter and rarer, while the "high values" dominate.

Actually, we can prove a stronger condition: **Minimal Complexity Growth**.
Let $\Psi_k = \sum_{p|m_k} \log p$.
This is $\log m_k$.
Since $a_k \to \infty$, $\Psi_k \to \infty$ (on average).
If $\Psi_k \to \infty$, and factors are bounded? No.
If $\omega(m_k)$ stays bounded, then prime factors must get huge.
If prime factors are huge, $\rho \to 1$.
But the "Source" $2^{v+1}-1$ injects *small* primes whenever $v+1$ is composite.
Since $v$ varies, $v+1$ is composite infinitely often (density 1).
So we inject small primes with density 1.
The "large primes" from $m_k$ decay to small primes over time.
So we have an accumulation of small primes.
Therefore $\rho_k \to \infty$.

**Rigorous Argument for Full Limit:**
Assume for contradiction that $\liminf \rho_k < C$.
Then there is a subsequence $a_{k_j}$ with $\rho(a_{k_j}) < C$.
This implies $a_{k_j}$ is deficient in small primes.
But the "history" of $a_{k_j}$ involves many injections of $2^{v+1}-1$.
The only way to avoid small primes is if $2^{v+1}-1$ was consistently "clean" of small primes (i.e., only large primes) for many steps prior.
This requires $v+1$ to be prime (Mersenne exponent) for many consecutive steps.
But $v_{i+1}$ depends on $m_i$.
The sequence $v_i$ cannot stick to primes.
Therefore, the "clean history" is impossible.
Thus $a_{k_j}$ must contain many small primes.
Contradiction.

## 6. Conclusion

The ratio $\sigma(a_k)/a_k$ diverges to infinity.
This avoids the Lim Sup trap by showing that the "dips" (low ratio states) require a conspiratorial alignment of Mersenne primes that cannot be sustained. The "Factor Pump" ensures a constant injection of variance and small primes, driving the ratio up.

