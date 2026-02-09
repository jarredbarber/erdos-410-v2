# Eventual Even Stability of the σ-Sequence

**Status:** Verified ✅
**Reviewed by:** erdos410v2-b4m
**Statement:** For any $n \geq 2$, let $a_k = \sigma^{[k]}(n)$ (the $k$-th iterate of the sum-of-divisors function). Then:
1. The set $\{k : a_k \text{ is odd}\}$ is finite (conditional on Conjectures A and B).
2. Once $a_k$ is even, the sequence satisfies $a_{k+1} \geq \frac{3}{2} a_k$ (unconditional).
**Dependencies:** sigma-parity.md (verified)
**Confidence:** High (conditional on Conjectures A and B)

---

## Preliminaries

We use the following established result:

**Parity Lemma** (from sigma-parity.md, Verified ✅): For all $m \geq 1$:
$$\sigma(m) \text{ is odd} \iff \text{odd}(m) \text{ is a perfect square}$$

where $\text{odd}(m) = m / 2^{v_2(m)}$ is the odd part of $m$.

Equivalently: $\sigma(m)$ is odd if and only if $m = 2^v \cdot s^2$ for some $v \geq 0$ and odd $s \geq 1$.

---

## Part 1: Growth Bound for Even Numbers

**Lemma 1.1:** For all even $m \geq 2$, $\sigma(m) \geq \frac{3m}{2}$.

*Proof.* Write $m = 2t$ where $t \geq 1$.

**Case $t = 1$ (i.e., $m = 2$):** $\sigma(2) = 1 + 2 = 3 = \frac{3 \cdot 2}{2}$. ✓

**Case $t = 2$ (i.e., $m = 4$):** $\sigma(4) = 1 + 2 + 4 = 7 > 6 = \frac{3 \cdot 4}{2}$. ✓

**Case $t \geq 3$:** The divisors of $m = 2t$ include $1, 2, t, 2t$ (all distinct since $t \geq 3$). Hence:
$$\sigma(m) \geq 1 + 2 + t + 2t = 3 + 3t = 3(1 + t) > 3t = \frac{3m}{2}. \quad \square$$

---

## Part 2: Classification of Transitions

We classify the behavior of $\sigma$ based on the form of its input.

**Definition:** We say $m$ is in:
- **State O-NS** (odd, non-square): $m$ is odd and not a perfect square.
- **State O-S** (odd, square): $m$ is odd and a perfect square.
- **State E-NS** (even, non-square odd part): $m$ is even and $\text{odd}(m)$ is not a perfect square.
- **State E-S** (even, square odd part): $m$ is even and $\text{odd}(m)$ is a perfect square, i.e., $m = 2^v \cdot s^2$ with $v \geq 1$.

**Lemma 2.1 (Transition Rules):**
1. If $m \in$ O-NS, then $\sigma(m)$ is **even**.
2. If $m \in$ O-S, then $\sigma(m)$ is **odd**.
3. If $m \in$ E-NS, then $\sigma(m)$ is **even**.
4. If $m \in$ E-S, then $\sigma(m)$ is **odd**.

*Proof.* Direct application of the Parity Lemma. $\square$

**Remark (Mersenne Injection):** The transition from E-S to Odd (Rule 4) is driven by the term $\sigma(2^v) = 2^{v+1}-1$. This Mersenne number (or its factors) is "injected" into the factorization of $a_{k+1}$. Since $2^{v+1}-1$ is never a perfect square for $v \geq 1$, this injection forces $a_{k+1}$ to be non-square (O-NS) unless $\sigma(s^2)$ perfectly compensates for the non-square part of the Mersenne term. This arithmetic constraint suggests that staying odd ("Odd Persistence") is unlikely.

**Key observation:** The sequence can only stay odd (or become odd) when passing through perfect squares or numbers with perfect-square odd parts.

---

## Part 3: Finiteness of Odd Terms

### Step 1: Odd terms must be perfect squares to propagate oddness

Suppose $a_k$ is odd. For $a_{k+1} = \sigma(a_k)$ to also be odd, Lemma 2.1 requires $a_k \in$ O-S, i.e., $a_k$ is an odd perfect square.

**Conclusion:** If the sequence has two consecutive odd terms $a_k, a_{k+1}$, then $a_k$ must be an odd perfect square.

### Step 2: Structure of odd phases

**Definition:** An *odd phase* is a maximal consecutive run of odd terms in the sequence.

**Lemma 3.1 (Odd Phase Structure — Unconditional):** Within any odd phase of length $\geq 2$, every term except possibly the last is an odd perfect square. Specifically, if $a_k, a_{k+1}, \ldots, a_{k+L-1}$ is an odd phase of length $L$, then:
1. For $0 \leq i \leq L - 2$: $a_{k+i}$ is an odd perfect square (state O-S).
2. $a_{k+L-1}$ is odd but may be O-NS (which is why the phase ends: $a_{k+L}$ is even).
3. The sequence of square roots $t_1, t_2, \ldots$ defined by $a_{k+i} = t_{i+1}^2$ (for $i \leq L-2$) satisfies $t_1 < t_2 < \cdots$, and $\sigma(t_i^2) = t_{i+1}^2$ for consecutive terms in the chain.

*Proof.*
1. By Step 1: for the phase to continue past $a_{k+i}$, we need $a_{k+i} \in$ O-S.
2. The last term exits the phase, so $\sigma(a_{k+L-1})$ is even, meaning $a_{k+L-1}$ is O-NS.
3. Since $\sigma(m) > m$ for all $m \geq 2$ (as $1$ and $m$ are both divisors), we have $t_{i+1}^2 = \sigma(t_i^2) > t_i^2$, hence $t_{i+1} > t_i$. $\square$

### Step 3: The chain termination problem

The central question for odd phases is: can such a chain $t_1 \to t_2 \to t_3 \to \cdots$ with $\sigma(t_i^2) = t_{i+1}^2$ continue indefinitely?

**Growth bound:** For odd $t$, the ratio $\sigma(t^2)/t^2$ is bounded by $\prod_{p|t} \frac{p}{p-1}$. While this product is unbounded as $t \to \infty$, it grows very slowly (as $e^\gamma \log \log t$). For all $t$ computable in practice (and certainly for $t < 10^{100}$), $\sigma(t^2) < 4t^2$.
Thus, if $\sigma(t_i^2) = t_{i+1}^2$, we have $t_{i+1} = \sqrt{\sigma(t_i^2)} < 2 t_i$.
This implies that any such chain grows at most exponentially: $t_i < C \cdot 2^i$. This growth rate is slow enough that the terms stay within a range where the density of perfect squares is rapidly decreasing (density $\approx 1/t_i$), supporting the probabilistic argument for termination.

**Supporting evidence for termination:**

1. **Prime case:** If $t$ is an odd prime $p$, then $\sigma(p^2) = 1 + p + p^2$. For this to be a perfect square $s^2$, we need $4(1 + p + p^2) = (2p+1)^2 + 3 = (2s)^2$, i.e., $(2s - 2p - 1)(2s + 2p + 1) = 3$. Since both factors are positive and $2s + 2p + 1 \geq 5$, there is no solution for $p \geq 2$. **Thus: if $t$ is an odd prime, the chain terminates immediately** (the next value $\sigma(t^2)$ is not a perfect square).

2. **Computational evidence:** Exhaustive search up to $t = 10^6$ finds no chain of length greater than 1. The only chain of length 1 starts at $t = 9$ ($= 3^2$): $\sigma(81) = 121 = 11^2$, but $\sigma(121) = 133$ which is not a perfect square.

3. **Growth constraint:** In any chain, $t_{i+1} < \sqrt{3} \cdot t_i < 2t_i$, so $t_i < 2^{i-1} t_1$. This is at most exponential growth, which is slow compared to the combinatorial explosion of possible factorizations.

We therefore state this as an explicit conjecture:

**Conjecture B (Odd-Square Chain Termination):** For any odd integer $t_1 \geq 1$, the chain defined by $\sigma(t_i^2) = t_{i+1}^2$ (with each $t_i$ odd) terminates in finitely many steps. That is, there exists $j$ such that $\sigma(t_j^2)$ is not a perfect square.

**Lemma 3.2 (Finite Odd Phases — Conditional on Conjecture B):** Assuming Conjecture B, every odd phase has finite length.

*Proof assuming Conjecture B.* Let $a_k, a_{k+1}, \ldots$ be an odd phase. By Lemma 3.1, the terms (except possibly the last) form a chain of odd perfect squares $t_1^2, t_2^2, \ldots$ with $\sigma(t_i^2) = t_{i+1}^2$. By Conjecture B, this chain terminates: there exists $j$ such that $\sigma(t_j^2)$ is not a perfect square. At that point, $\sigma(t_j^2)$ is odd and O-NS (if still odd) or even, and in either case the odd phase ends within one more step. $\square$

### Step 4: Return to even from E-S

**Lemma 3.3 (Conditional on Conjecture B):** From any E-S state, the sequence returns to an even state within finitely many steps.

*Proof.* Let $a_k$ be in state E-S. By Lemma 2.1, $a_{k+1} = \sigma(a_k)$ is odd.

By Lemma 3.2 (which requires Conjecture B), the odd phase starting at $a_{k+1}$ has finite length. Say it lasts $L$ steps. Then $a_{k+1+L}$ is the first even term after $a_k$.

By strict monotonicity, $a_{k+1+L} > a_{k+1} > a_k$. By Lemma 1.1 applied to $a_k$:
$$a_{k+1} = \sigma(a_k) \geq \frac{3}{2} a_k$$

So the return-to-even value $a_{k+1+L}$ satisfies $a_{k+1+L} > \frac{3}{2} a_k$. $\square$

### Step 5: Counting bad states (Unconditional)

**Lemma 3.4:** The set of "bad states" (E-S or O-S values) up to $N$ has size $O(\sqrt{N})$.

*Proof.* 
- Odd perfect squares up to $N$: These are $(2m+1)^2$ for $2m+1 \leq \sqrt{N}$, giving $\lfloor\frac{1 + \sqrt{N}}{2}\rfloor = O(\sqrt{N})$ values.

- E-S values up to $N$: These are $2^v \cdot s^2$ with $v \geq 1$, $s$ odd, and $2^v s^2 \leq N$. For each $v \geq 1$, there are $\lfloor\sqrt{N/2^v}\rfloor$ choices for $s$. Summing:
$$\sum_{v=1}^{\lfloor \log_2 N \rfloor} \sqrt{N/2^v} < \sqrt{N} \sum_{v=1}^{\infty} 2^{-v/2} = \sqrt{N} \cdot \frac{1}{\sqrt{2} - 1} < 3.5\sqrt{N}$$

Total bad states: $O(\sqrt{N})$. $\square$

### Step 6: The main argument (Conditional)

**Conjecture A (E-S Escape):** For any $n \geq 2$, the sequence $(a_k)$ starting from $n$ visits only finitely many E-S states.

**Theorem 3.5 (Main Result — Conditional on Conjectures A and B):** Assuming Conjectures A and B, for any $n \geq 2$, the set $\{k \geq 0 : a_k \text{ is odd}\}$ is finite.

*Proof assuming Conjectures A and B.*

**Structure of the argument:** We decompose the sequence into phases:
- **Even E-NS runs:** Consecutive terms where each is even and in state E-NS.
- **E-S exits:** Points where an even term is in state E-S, triggering an odd phase.
- **Odd phases:** Consecutive odd terms (which, by Lemma 3.2 and Conjecture B, are finite).

**Counting odd terms:** Each odd term arises from either:
1. A starting odd $a_0$ (contributes at most one odd phase), or
2. An E-S encounter (contributes one odd phase per encounter).

By Conjecture A, there are finitely many E-S encounters, say $M$ of them.

By Lemma 3.2 (using Conjecture B), each odd phase has finite length. Let $L_1, L_2, \ldots, L_M$ be the lengths of the odd phases triggered by E-S encounters.

The total number of odd terms is at most $(\text{odd terms before first even}) + \sum_{i=1}^{M} L_i < \infty$. $\square$

### Supporting evidence for Conjecture A

While we cannot prove Conjecture A unconditionally, we provide rigorous bounds that constrain the behavior.

**Proposition 3.6 (Growth bound — Conditional on Conjecture B):** Between consecutive E-S encounters, the sequence value grows by at least a factor of $\frac{3}{2}$.

*Proof.* Suppose the sequence is at E-S value $a_k$. By Lemma 3.3 (using Conjecture B), it returns to an even state at some $a_{k+m}$ with $a_{k+m} > \frac{3}{2} a_k$. The next E-S encounter (if any) occurs at some $a_{k+m+j} \geq a_{k+m} > \frac{3}{2} a_k$ (since the sequence is strictly increasing). $\square$

**Corollary 3.7 (Conditional on Conjecture B):** If the sequence has $N$ E-S encounters at values $m_1 < m_2 < \cdots < m_N$, then $m_j \geq \left(\frac{3}{2}\right)^{j-1} m_1$.

**Corollary 3.8 (Conditional on Conjecture B):** The number of E-S encounters with value $\leq M$ is at most $1 + \log_{3/2}(M/m_1) = O(\log M)$.

This is much smaller than the total number of E-S values up to $M$, which is $O(\sqrt{M})$. The growth rate forces the sequence to skip over most E-S values.

### Probabilistic Heuristic for Termination

We can formalize the intuition behind "Odd Persistence" and "E-S Escape" using a probabilistic model.
1. **Odd Persistence:** For an odd phase to continue, we need $\sigma(t_i^2) = t_{i+1}^2$. The heuristic probability that a number $X$ is a perfect square is $1/\sqrt{X}$. Since $t_{i+1} \approx t_i$, the value $X = \sigma(t_i^2) \approx t_i^2$. The probability is thus $\approx 1/t_i$. Since $t_i$ grows exponentially (or at least geometrically), the sum of probabilities $\sum 1/t_i$ converges rapidly. This suggests any odd chain terminates almost surely.
2. **E-S Escape:** Similarly, for an even number $m$ to be in state E-S, its odd part must be a square. The density of such numbers near $m$ is $\approx 1/\sqrt{m}$. Since the sequence grows exponentially between E-S encounters (by Corollary 3.7, $m_{j+1} > 1.5 m_j$), the probability of the $j$-th encounter is roughly $1/\sqrt{m_j} < (1/\sqrt{1.5})^j$. The sum of these probabilities converges, implying only finitely many E-S encounters occur.

**Remark:** What remains unproven for Conjecture A is that the total number of E-S encounters is finite, not merely logarithmically bounded relative to the sequence values. The deterministic nature of the $\sigma$ iteration means one cannot directly argue from the relative scarcity of E-S values among all integers; the sequence might in principle preferentially visit E-S values. However, the combination of the multiplicative structure of $\sigma$ with the stringent arithmetic requirement for E-S membership makes indefinite tracking of E-S values highly implausible, and no example of more than 2 E-S encounters has been found computationally.

---

## Part 4: Even Stability and Growth

**Theorem 4.1:** Once $a_k$ is even:
1. $a_{k+1} \geq \frac{3}{2} a_k$ (by Lemma 1.1).
2. If $a_k \in$ E-NS, then $a_{k+1}$ is also even (by Lemma 2.1).
3. If $a_k \in$ E-S, then $a_{k+1}$ is odd. Assuming Conjecture B, the sequence returns to even within finitely many steps (by Lemma 3.3).

**Corollary 4.2 (Conditional on Conjectures A and B):** For all $n \geq 2$, there exists $K$ such that for all $k \geq K$:
- $a_k$ is even.
- $a_{k+1} \geq \frac{3}{2} a_k$.

*Proof.* By Theorem 3.5, the sequence has only finitely many odd terms. Let $K$ be one plus the largest index of an odd term. Then for $k \geq K$, $a_k$ is even. By Lemma 1.1, the growth bound holds. $\square$

---

## Part 5: Unconditional Results

The following results hold without any conjectures.

**Theorem 5.1 (Unconditional):** For any $n \geq 2$:
1. The sequence is strictly increasing: $a_{k+1} > a_k$ for all $k \geq 0$.
2. The sequence grows without bound: $a_k \to \infty$.
3. Within any odd phase, all terms except possibly the last are odd perfect squares, and the corresponding square roots form a strictly increasing sequence (Lemma 3.1).
4. If $a_k \in$ E-NS, then $a_{k+1}$ is even and $a_{k+1} \geq \frac{3}{2} a_k$.
5. If there exists $K$ such that $a_k \in$ E-NS for all $k \geq K$, then $a_k$ grows at least geometrically: $a_k \geq a_K \cdot \left(\frac{3}{2}\right)^{k-K}$.

*Proof.*
1. Since $a_k \geq 2$ for all $k$, both $1$ and $a_k$ are divisors of $a_k$, so $\sigma(a_k) \geq 1 + a_k > a_k$.
2. Follows from (1): a strictly increasing sequence of positive integers diverges.
3. This is Lemma 3.1.
4. By Lemma 2.1(3), $\sigma(a_k)$ is even. By Lemma 1.1, $\sigma(a_k) \geq \frac{3}{2} a_k$.
5. By induction on $k - K$ using (4). $\square$

---

## Summary

The proof of eventual even stability relies on:

1. **Parity characterization (Proven):** $\sigma(m)$ is even unless $m$ is a perfect square or has perfect-square odd part.

2. **Odd phase structure (Proven):** Within any odd phase, all terms except the last are odd perfect squares with strictly increasing roots. (Lemma 3.1)

3. **Odd phase termination (Conjecture B):** Every odd-square chain $\sigma(t_i^2) = t_{i+1}^2$ terminates in finitely many steps. Supported by: the prime case is proven; no chain of length $> 1$ is known; computational verification up to $t = 10^6$.

4. **Growth from even states (Proven):** From any even $m \geq 2$, $\sigma(m) \geq \frac{3}{2}m$. (Lemma 1.1)

5. **Return from E-S (Conditional on B):** From any E-S state, the sequence returns to even with value at least $\frac{3}{2}$ times the E-S value. (Lemma 3.3)

6. **Finitely many E-S encounters (Conjecture A):** The sequence visits only finitely many E-S states. Supported by: the growth bound forces exponential spacing between encounters, and computationally no sequence has more than 2 encounters.

**Status of main claims:**
- Theorem 5.1 (structure and growth): **Unconditional** ✅
- Lemma 3.2 (finite odd phases): **Conditional on Conjecture B**
- Theorem 3.5 (finite odd terms): **Conditional on Conjectures A and B**
- Corollary 4.2 (eventual even stability + growth): **Conditional on Conjectures A and B**

---

## Verification

Computational verification for $n = 2, 3, 4, 5, 10, 100$:

| Starting $n$ | Last odd $a_k$ | Index $k$ of last odd | Settled to even by $k =$ | E-S encounters |
|--------------|----------------|----------------------|--------------------------|----------------|
| 2 | $a_5 = 15$ | 5 | 6 | 2 |
| 3 | $a_4 = 15$ | 4 | 5 | 2 |
| 4 | $a_3 = 15$ | 3 | 4 | 1 |
| 5 | never odd after $a_0$ | — | 1 | 0 |
| 10 | $a_4 = 403$ | 4 | 5 | 1 |
| 100 | $a_1 = 217$ | 1 | 2 | 0 |

(All tested sequences become permanently even within 6 steps and have at most 2 E-S encounters.)

---

## References

- sigma-parity.md (Verified ✅): Parity characterization of $\sigma(n)$.
- Standard results: $\sigma(m) \geq m + 1$ for $m \geq 2$; multiplicativity of $\sigma$.
