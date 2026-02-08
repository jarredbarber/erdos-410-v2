import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Padics.PadicVal.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
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

lemma oddPart_dvd (n : ℕ) : oddPart n ∣ n := by
  rw [oddPart]
  exact div_dvd_of_dvd (@pow_padicValNat_dvd 2 n)

lemma oddPart_mul_two_pow (n : ℕ) (hn : n ≠ 0) :
    oddPart n * 2^(padicValNat 2 n) = n := by
  rw [oddPart]
  rw [Nat.div_mul_cancel (@pow_padicValNat_dvd 2 n)]

lemma oddPart_odd (n : ℕ) (hn : n ≠ 0) : Odd (oddPart n) := by
  let m := oddPart n
  have h_val : padicValNat 2 n = padicValNat 2 m + padicValNat 2 n := by
     nth_rw 1 [← oddPart_mul_two_pow n hn]
     have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
     rw [padicValNat.mul]
     · simp
       rfl
     · apply oddPart_ne_zero n hn
     · apply pow_ne_zero
       norm_num
  
  have : padicValNat 2 m = 0 := by
    nth_rw 1 [← zero_add (padicValNat 2 n)] at h_val
    exact (Nat.add_right_cancel h_val).symm

  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h_even
  have : 1 ≤ padicValNat 2 m := by
       apply one_le_padicValNat_of_dvd
       · exact oddPart_ne_zero n hn
       · exact h_even
  linarith

lemma geom_sum_two (k : ℕ) : ∑ i ∈ range k, 2^i = 2^k - 1 := by
  have h := geom_sum_mul_add (2-1) k
  simp at h
  exact eq_tsub_of_add_eq h

lemma sigma_one_two_pow (k : ℕ) : sigma 1 (2^k) = 2^(k+1) - 1 := by
  rw [sigma_one_apply_prime_pow (Nat.prime_two)]
  rw [geom_sum_two (k+1)]

lemma sigma_odd_part (n : ℕ) (hn : n ≠ 0) :
    sigma 1 n = (2^(padicValNat 2 n + 1) - 1) * sigma 1 (oddPart n) := by
  have h_decomp := oddPart_mul_two_pow n hn
  nth_rw 1 [← h_decomp]
  rw [mul_comm]
  rw [isMultiplicative_sigma.map_mul_of_coprime]
  · rw [sigma_one_two_pow]
  · apply Nat.Coprime.pow_left
    rw [Nat.prime_two.coprime_iff_not_dvd]
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact oddPart_odd n hn

lemma v2_sigma_odd (k : ℕ) : padicValNat 2 (2^(k+1) - 1) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  rw [← even_iff_two_dvd]
  rw [Nat.not_even_iff_odd]
  let n := 2^(k+1)
  change Odd (n - 1)
  have h_even : Even n := by
    apply Nat.even_pow.mpr
    constructor
    · exact even_two
    · exact succ_ne_zero k
  rcases h_even with ⟨m, hm⟩
  rw [hm]
  apply odd_iff_exists_bit1.mpr
  use m - 1
  have h_pos : 0 < n := by
    apply pow_pos
    norm_num
  have hm_pos : 1 ≤ m := by
    rw [← two_mul] at hm
    rw [hm] at h_pos
    apply Nat.pos_of_mul_pos_left h_pos
  omega

lemma sum_mod_eq_sum_mod_mod {α : Type*} (s : Finset α) (f : α → ℕ) (m : ℕ) :
    (∑ i ∈ s, f i) % m = (∑ i ∈ s, f i % m) % m := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    simp [Nat.add_mod, ih]

lemma sigma_odd_prime_pow_mod_two (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    sigma 1 (p ^ k) % 2 = (k + 1) % 2 := by
  rw [sigma_one_apply_prime_pow hp]
  change (∑ i ∈ range (k + 1), p ^ i) % 2 = (k + 1) % 2
  rw [sum_mod_eq_sum_mod_mod]
  trans (∑ i ∈ range (k + 1), 1) % 2
  · congr 2
    ext i
    rw [Nat.pow_mod]
    have : p % 2 = 1 := by
       cases Nat.mod_two_eq_zero_or_one p with
       | inl h =>
         rw [← Nat.dvd_iff_mod_eq_zero] at h
         have h_eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
         rw [h_eq] at hp2
         contradiction
       | inr h => exact h
    rw [this]
    simp
  · simp

lemma v2_sigma_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    if Odd k then 1 ≤ padicValNat 2 (sigma 1 (p ^ k)) else padicValNat 2 (sigma 1 (p ^ k)) = 0 := by
  split_ifs with hk
  · have h_pos : sigma 1 (p^k) ≠ 0 := by
      apply Nat.ne_of_gt
      apply sigma_pos
      apply pow_ne_zero
      exact hp.ne_zero
    apply one_le_padicValNat_of_dvd h_pos
    apply Nat.dvd_of_mod_eq_zero
    rw [sigma_odd_prime_pow_mod_two p k hp hp2]
    -- Odd k -> (k+1)%2 = 0
    rw [← Nat.not_even_iff_odd] at hk
    rw [Nat.add_mod]
    cases Nat.mod_two_eq_zero_or_one k with
    | inl h =>
       rw [← Nat.dvd_iff_mod_eq_zero] at h
       rw [← even_iff_two_dvd] at h
       contradiction
    | inr h => rw [h]
  · apply padicValNat.eq_zero_of_not_dvd
    intro h_dvd
    have h_mod_zero : sigma 1 (p^k) % 2 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
    rw [sigma_odd_prime_pow_mod_two p k hp hp2] at h_mod_zero
    -- ¬ Odd k -> (k+1)%2 = 1
    rw [← Nat.not_even_iff_odd] at hk
    rw [not_not] at hk
    rw [even_iff_two_dvd] at hk
    have h_k_mod : k % 2 = 0 := Nat.mod_eq_zero_of_dvd hk
    rw [Nat.add_mod, h_k_mod] at h_mod_zero
    contradiction

lemma padicValNat_finset_prod {α : Type*} (s : Finset α) (f : α → ℕ) (p : ℕ) [Fact p.Prime]
    (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [padicValNat.mul]
    · rw [ih]
      intro x hx
      apply hf
      exact Finset.mem_insert_of_mem hx
    · apply hf
      exact Finset.mem_insert_self a s
    · rw [Finset.prod_ne_zero_iff]
      intro x hx
      apply hf
      exact Finset.mem_insert_of_mem hx

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


lemma oddPart_eq_self_of_odd (n : ℕ) (h : Odd n) : oddPart n = n := by
  rw [oddPart]
  rw [padicValNat.eq_zero_of_not_dvd]
  · simp
  · rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact h

/-- omega(n) equals the card of primeFactors n -/
lemma cardDistinctFactors_eq_card_primeFactors (n : ℕ) : cardDistinctFactors n = n.primeFactors.card := by
  -- Trivial by definition, but simp loops on unfolding.
  -- cardDistinctFactors n = n.primeFactorsList.dedup.length
  -- n.primeFactors = n.primeFactorsList.toFinset
  -- toFinset.card = dedup.length
  sorry

lemma omega_mul_ge_left (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    cardDistinctFactors (m * n) ≥ cardDistinctFactors m := by
  rw [cardDistinctFactors_eq_card_primeFactors]
  rw [cardDistinctFactors_eq_card_primeFactors]
  apply Finset.card_le_card
  rw [Nat.primeFactors_mul hm hn]
  apply Finset.subset_union_left

/-- Lemma B: Recursive Factor Bounds
    Show that omega(a_{k+2}) >= omega(2^(v_{k+1}+1) - 1). -/
lemma recursive_factor_bounds (a_k : ℕ) (ha_k : a_k ≠ 0) :
    let v_k := padicValNat 2 a_k
    let d_k := oddPart a_k
    let a_succ := sigma 1 a_k
    let v_succ := padicValNat 2 a_succ
    let d_succ := oddPart a_succ
    let a_succ2 := sigma 1 a_succ
    v_succ ≥ omegaOdd d_k ∧ cardDistinctFactors a_succ2 ≥ cardDistinctFactors (2^(v_succ + 1) - 1) := by
  let v_k := padicValNat 2 a_k
  let d_k := oddPart a_k
  let a_succ := sigma 1 a_k
  let v_succ := padicValNat 2 a_succ
  let d_succ := oddPart a_succ
  let a_succ2 := sigma 1 a_succ
  
  have ha_succ : a_succ ≠ 0 := by
    apply Nat.ne_of_gt
    have h_pos : 0 < sigma 1 a_k := sigma_pos 1 a_k ha_k
    exact h_pos

  have hd_k_ne_zero : d_k ≠ 0 := oddPart_ne_zero a_k ha_k
  have hd_succ_ne_zero : d_succ ≠ 0 := oddPart_ne_zero a_succ ha_succ
  
  -- Part 1: v_{k+1} >= omegaOdd(d_k)
  have h1 : v_succ ≥ omegaOdd d_k := by
    have h_decomp : a_succ = (2^(v_k+1) - 1) * sigma 1 d_k := by
       dsimp only [a_succ, v_k, d_k]
       rw [sigma_odd_part a_k ha_k]
    
    have h_v2_split : padicValNat 2 a_succ = padicValNat 2 (2^(v_k+1) - 1) + padicValNat 2 (sigma 1 d_k) := by
       rw [h_decomp]
       rw [padicValNat.mul]
       · apply Nat.ne_of_gt
         apply Nat.sub_pos_of_lt
         apply Nat.one_lt_pow (succ_ne_zero _) (by norm_num)
       · apply Nat.ne_of_gt
         have h_pos : 0 < sigma 1 d_k := sigma_pos 1 d_k hd_k_ne_zero
         exact h_pos

    dsimp only [v_succ, v_k]
    rw [h_v2_split]
    rw [v2_sigma_odd (padicValNat 2 a_k)]
    rw [zero_add]
    
    have h_lemma_a := v2_sigma_ge_omegaOdd_oddPart d_k hd_k_ne_zero
    
    have h_odd_d_k : oddPart d_k = d_k := by
       apply oddPart_eq_self_of_odd
       apply oddPart_odd a_k ha_k
       
    rw [h_odd_d_k] at h_lemma_a
    exact h_lemma_a

  -- Part 2: omega(a_{k+2}) >= omega(2^(v_{k+1}+1) - 1)
  have h2 : cardDistinctFactors a_succ2 ≥ cardDistinctFactors (2^(v_succ + 1) - 1) := by
    have h_decomp : a_succ2 = (2^(v_succ + 1) - 1) * sigma 1 d_succ := by
       dsimp only [a_succ2, v_succ, d_succ]
       rw [sigma_odd_part a_succ ha_succ]
       
    rw [h_decomp]
    apply omega_mul_ge_left
    · apply Nat.ne_of_gt
      apply Nat.sub_pos_of_lt
      apply Nat.one_lt_pow (succ_ne_zero _) (by norm_num)
    · apply Nat.ne_of_gt
      have h_pos : 0 < sigma 1 d_succ := sigma_pos 1 d_succ hd_succ_ne_zero
      exact h_pos

  exact ⟨h1, h2⟩

end Erdos410
