# Literature Directory

Index of natural language proofs for Erdős Problem #410.

## Problem

For all $n \geq 2$, does $\lim_{k \to \infty} \sigma_k(n)^{1/k} = \infty$?

Where $\sigma_1(n) = \sigma(n)$ (sum of divisors) and $\sigma_k(n) = \sigma(\sigma_{k-1}(n))$.

## Verified Results

| File | Statement | Status |
|------|-----------|--------|
| [sigma-lower-bounds.md](sigma-lower-bounds.md) | $\sigma(n) \geq n+1$, $\sigma(2k) \geq 3k$ | Verified ✅ |
| [sigma-parity.md](sigma-parity.md) | $\sigma(n)$ odd iff $n=k^2$ or $2k^2$ | Verified ✅ |
| [smooth-escape.md](smooth-escape.md) | Orbit leaves any finite set of primes | Verified ✅ |
| [omega-lower-bounds.md](omega-lower-bounds.md) | $\omega(2^n-1) \ge \tau(n)-2$ and Mersenne Instability | Verified ✅ |

## In Progress / Under Review

| File | Statement | Status |
|------|-----------|--------|
| [main-assembly-v2.md](main-assembly-v2.md) | Proof assembly (waiting on ratio lemma) | Under review 🔍 |
| [eventual-even-stability.md](eventual-even-stability.md) | Eventually even stability | Draft ✏️ |
| [main-theorem-v2.md](main-theorem-v2.md) | Full proof attempt v2 | Draft ✏️ |
| [main-theorem.md](main-theorem.md) | Full proof attempt v1 | Draft ✏️ |

## Rejected / Dead Ends

| File | Statement | Status |
|------|-----------|--------|
| [omega-divergence.md](omega-divergence.md) | $\omega(a_k) \to \infty$ via Zsygmondy | Rejected ❌ |
| [ratio-divergence.md](ratio-divergence.md) | $\sigma(a_k)/a_k \to \infty$ via ratio | Rejected ❌ |
| [ratio-divergence-v2.md](ratio-divergence-v2.md) | Ratio divergence v2 | Rejected ❌ |
| [ratio-divergence-energy.md](ratio-divergence-energy.md) | Ratio via energy | Rejected ❌ |
| [ratio-divergence-energy-v2.md](ratio-divergence-energy-v2.md) | Ratio via energy v2 | Rejected ❌ |
| [ratio-divergence-full.md](ratio-divergence-full.md) | Ratio via factor pump + dynamics | Rejected ❌ |

See also `dead-ends.md` for detailed failure analysis.
