import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Nat ArithmeticFunction Finset
open scoped Classical

namespace Erdos410

/-- omega_odd(n) is the number of prime factors of n that appear with an odd exponent. -/
def omegaOdd (n : ℕ) : ℕ :=
  (n.primeFactors.filter (fun p => Odd (padicValNat p n))).card

/-- The odd part of n. -/
def oddPart (n : ℕ) : ℕ := n / 2^(padicValNat 2 n)

lemma oddPart_ne_zero (n : ℕ) (hn : n ≠ 0) : oddPart n ≠ 0 := by
  rw [oddPart]
  apply Nat.ne_of_gt
  apply Nat.div_pos
  · apply Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
    apply pow_padicValNat_dvd
  · apply pow_pos (by norm_num) _

lemma oddPart_odd (n : ℕ) (hn : n ≠ 0) : Odd (oddPart n) := sorry

lemma oddPart_dvd (n : ℕ) : oddPart n ∣ n := by
  rw [oddPart]
  exact div_dvd_of_dvd (@pow_padicValNat_dvd 2 n)

lemma oddPart_mul_two_pow (n : ℕ) (hn : n ≠ 0) :
    oddPart n * 2^(padicValNat 2 n) = n := by
  rw [oddPart]
  rw [Nat.div_mul_cancel (@pow_padicValNat_dvd 2 n)]

lemma geom_sum_two (k : ℕ) : ∑ i ∈ range k, 2^i = 2^k - 1 := sorry

lemma sigma_one_two_pow (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := sorry

lemma sigma_odd_part (n : ℕ) (hn : n ≠ 0) :
    sigma 1 n = (2^(padicValNat 2 n + 1) - 1) * sigma 1 (oddPart n) := sorry

lemma v2_sigma_odd (k : ℕ) : padicValNat 2 (2^(k+1) - 1) = 0 := sorry

lemma sigma_odd_prime_pow_mod_two (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    sigma 1 (p ^ k) % 2 = (k + 1) % 2 := sorry

lemma v2_sigma_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    if Odd k then 1 ≤ padicValNat 2 (sigma 1 (p ^ k)) else padicValNat 2 (sigma 1 (p ^ k)) = 0 := sorry

lemma padicValNat_finset_prod {α : Type*} (s : Finset α) (f : α → ℕ) (p : ℕ) [Fact p.Prime]
    (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := sorry

lemma sigma_prod_prime_pow_eq (n : ℕ) (hn : n ≠ 0) :
    sigma 1 n = ∏ p ∈ n.primeFactors, sigma 1 (p ^ (padicValNat p n)) := by
  let f := sigma 1
  have h_mult : IsMultiplicative f := isMultiplicative_sigma
  let g := fun p => p ^ (padicValNat p n)
  have h_decomp : n = ∏ p ∈ n.primeFactors, g p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod]
    rw [Nat.support_factorization]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.factorization_def n (Nat.mem_primeFactors.mp hp).1]
  conv_lhs => rw [h_decomp]
  -- map_prod takes g first
  rw [IsMultiplicative.map_prod g h_mult]
  · intro p hp q hq hpq
    apply Nat.coprime_pow_primes _ _ (Nat.mem_primeFactors.mp hp).1 (Nat.mem_primeFactors.mp hq).1 hpq

/-- Lemma A: v2(sigma(n)) >= omega_odd(oddPart n) -/
lemma v2_sigma_ge_omegaOdd_oddPart (n : ℕ) (hn : n ≠ 0) :
    padicValNat 2 (sigma 1 n) ≥ omegaOdd (oddPart n) := by
  let m := oddPart n
  have hm : m ≠ 0 := oddPart_ne_zero n hn
  have hm_odd : Odd m := oddPart_odd n hn
  rw [sigma_odd_part n hn]
  have h_part1 : 2^(padicValNat 2 n + 1) - 1 ≠ 0 := by
    apply Nat.ne_of_gt
    have : 1 < 2^(padicValNat 2 n + 1) := by
      apply Nat.one_lt_pow (succ_ne_zero _) (by norm_num)
    exact Nat.sub_pos_of_lt this
  have h_part2 : sigma 1 m ≠ 0 := Nat.ne_of_gt (sigma_pos 1 m hm)
  rw [padicValNat.mul h_part1 h_part2]
  rw [v2_sigma_odd]
  rw [zero_add]
  rw [sigma_prod_prime_pow_eq m hm]
  have h_factors_nonzero : ∀ p ∈ m.primeFactors, sigma 1 (p ^ padicValNat p m) ≠ 0 := by
    intro p hp
    apply Nat.ne_of_gt
    apply sigma_pos
    apply pow_ne_zero
    exact Nat.Prime.ne_zero (Nat.mem_primeFactors.mp hp).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_finset_prod _ _ 2 h_factors_nonzero]
  rw [omegaOdd]
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p hp
  let e := padicValNat p m
  have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hp_odd : p ≠ 2 := by
    intro h; subst h
    have : 2 ∣ m := Nat.dvd_of_mem_primeFactors hp
    rw [← Nat.not_even_iff_odd] at hm_odd
    have : Even m := even_iff_two_dvd.mpr this
    contradiction
  have h_lem := v2_sigma_odd_prime_pow p e hp_prime hp_odd
  simp only [e] at h_lem
  by_cases h_e_odd : Odd e
  · rw [if_pos h_e_odd] at h_lem
    rw [if_pos h_e_odd]
    exact h_lem
  · rw [if_neg h_e_odd] at h_lem
    rw [if_neg h_e_odd]
    rw [h_lem]

end Erdos410
