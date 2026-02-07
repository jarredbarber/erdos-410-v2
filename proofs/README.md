# Literature Directory

Index of natural language proofs for Erdős Problem #410.

## Problem

For all $n \geq 2$, prove that $\lim_{k \to \infty} \sigma_k(n)^{1/k} = \infty$.

Where $\sigma_1(n) = \sigma(n)$ (sum of divisors) and $\sigma_k(n) = \sigma(\sigma_{k-1}(n))$.

## Results

| File | Statement | Status |
|------|-----------|--------|
| `sigma-lower-bounds.md` | σ(n) ≥ n+1 for n ≥ 2; σ(n) ≥ (√n+1)² for composite n; σ(n) ≥ 3n/2 for even n | Pending |
| `sigma-parity.md` | σ(n) is odd iff n is a perfect square or twice a perfect square | Pending |
| `main-theorem.md` | For all n ≥ 2, σ_k(n)^{1/k} → ∞ | Draft ✏️ |

## Proof Architecture

The main theorem decomposes into:
1. **Divergence**: σ^k(n) → ∞ (from σ(n) ≥ n+1)
2. **Exponential growth**: σ(n) ≥ 3n/2 for even n gives base exponential rate
3. **Super-exponential growth**: The growth rate increases without bound as iterates acquire more small prime factors
