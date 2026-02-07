import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Tendsto

open ArithmeticFunction Filter

namespace Erdos410

/-! ## Helper lemmas for σ bounds

These are sorry-ed statements to be filled in once natural language proofs
are verified. They form the key building blocks for the main Erdős 410 theorem.

### Key facts used:
- `sigma_apply`: `σ k n = ∑ d ∈ divisors n, d ^ k`
- `sigma_one_apply`: `σ 1 n = ∑ d ∈ divisors n, d`
- `sigma_pos`: `0 < σ k n` when `n ≠ 0`
- `isMultiplicative_sigma`: `σ k` is multiplicative
-/

/-- For n ≥ 2, σ₁(n) ≥ n + 1 (since 1 and n are always divisors). -/
lemma sigma_one_ge (n : ℕ) (hn : 2 ≤ n) : n + 1 ≤ sigma 1 n := by
  rw [sigma_one_apply]
  have h1n : (1 : ℕ) ≠ n := by omega
  have h1_mem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    rw [Finset.insert_subset_iff]
    exact ⟨h1_mem, Finset.singleton_subset_iff.mpr hn_mem⟩
  have hpair : ∑ d ∈ ({1, n} : Finset ℕ), (d : ℕ) = 1 + n := Finset.sum_pair h1n
  have hle : ∑ d ∈ ({1, n} : Finset ℕ), (d : ℕ) ≤ ∑ d ∈ n.divisors, d :=
    Finset.sum_le_sum_of_subset (f := fun (d : ℕ) => d) hsub
  linarith

/-- For even n ≥ 2, σ₁(n) ≥ 3n/2 (since 1, n/2, and n are all divisors).
    Stated as `3 * n ≤ 2 * σ₁(n)` to avoid natural number division. -/
lemma sigma_one_even_ge (n : ℕ) (hn : 2 ≤ n) (heven : Even n) :
    3 * n ≤ 2 * sigma 1 n := by
  sorry

/-- For n ≥ 2, the iterated σ₁ sequence tends to infinity.
    This is a key intermediate result: since σ₁(n) ≥ n + 1 for n ≥ 2,
    the iterates are strictly increasing and unbounded. -/
lemma sigma_one_iterate_tendsto_atTop (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun k => (sigma 1)^[k] n) atTop atTop := by
  sorry

end Erdos410
