import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Nat.Parity
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Erdos.Basic

open Nat Finset ArithmeticFunction

namespace Erdos410

/-- Number of distinct prime factors of n. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- Number of divisors of n. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- A primitive prime divisor of 2^n - 1 is a prime p such that p | 2^n - 1
    and p does not divide 2^k - 1 for any k < n with k > 0.
    We also require n ≠ 0 to avoid triviality. -/
def is_primitive_divisor (p n : ℕ) : Prop :=
  n ≠ 0 ∧ p.Prime ∧ p ∣ (2^n - 1) ∧ ∀ k < n, k > 0 → ¬(p ∣ (2^k - 1))

/-- Zsigmondy's Theorem for a=2, b=1:
    For all n > 1, except n = 6, 2^n - 1 has a primitive prime divisor. -/
axiom zsigmondy (n : ℕ) (hn : n > 1) (h6 : n ≠ 6) :
  ∃ p, is_primitive_divisor p n

lemma primitive_divisor_is_factor {p n : ℕ} (h : is_primitive_divisor p n) :
    p ∈ (2^n - 1).primeFactors := by
  rw [mem_primeFactors]
  have hn : n ≠ 0 := h.1
  have hpos : 2^n - 1 ≠ 0 := by
    apply Nat.ne_of_gt
    apply Nat.sub_pos_of_lt
    exact Nat.one_lt_two_pow hn (by norm_num)
  exact ⟨h.2.1, h.2.2.1, hpos⟩

lemma primitive_divisors_distinct {a b p : ℕ} (ha : is_primitive_divisor p a)
    (hb : is_primitive_divisor p b) : a = b := by
  rcases lt_trichotomy a b with h | rfl | h
  · obtain ⟨hb_ne, _, _, hprim⟩ := hb
    have : p ∣ 2^a - 1 := ha.2.2.1
    have : a > 0 := Nat.pos_of_ne_zero ha.1
    specialize hprim a h this
    contradiction
  · rfl
  · obtain ⟨ha_ne, _, _, hprim⟩ := ha
    have : p ∣ 2^b - 1 := hb.2.2.1
    have : b > 0 := Nat.pos_of_ne_zero hb.1
    specialize hprim b h this
    contradiction


/-- omega(2^n - 1) ≥ τ(n) - 2 -/
theorem omega_mersenne_lower_bound (n : ℕ) (hn : n ≥ 1) :
    omega (2^n - 1) ≥ tau n - 2 := by
  -- Define the set of divisors relevant for Zsigmondy
  let S := (n.divisors).filter (fun d => d ≠ 1 ∧ d ≠ 6)
  
  -- We claim there is an injection from S to prime factors of 2^n - 1
  -- For each d ∈ S, let p_d be a primitive prime divisor of 2^d - 1
  have h_zsig (d : ℕ) (hd : d ∈ S) : ∃ p, is_primitive_divisor p d := by
    simp only [S, mem_filter, mem_divisors] at hd
    have d_gt_1 : d > 1 := by
      rcases hd with ⟨⟨_, _⟩, hne1, _⟩
      exact Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero (by rintro rfl; simp at hd)) hne1.symm
    apply zsigmondy d d_gt_1 hd.2.2

  let p_map (d : ℕ) (hd : d ∈ S) : ℕ := Classical.choose (h_zsig d hd)
  
  have h_prim (d : ℕ) (hd : d ∈ S) : is_primitive_divisor (p_map d hd) d :=
    Classical.choose_spec (h_zsig d hd)

  -- The map is injective
  have h_inj : ∀ (a : ℕ) (ha : a ∈ S) (b : ℕ) (hb : b ∈ S),
      p_map a ha = p_map b hb → a = b := by
    intro a ha b hb heq
    apply primitive_divisors_distinct (h_prim a ha)
    rw [heq]
    exact h_prim b hb

  -- The image is a subset of prime factors of 2^n - 1
  let P := S.attach.image (fun ⟨d, hd⟩ => p_map d hd)
  
  have h_subset : P ⊆ (2^n - 1).primeFactors := by
    intro p hp
    rw [mem_image] at hp
    rcases hp with ⟨⟨d, hd⟩, _, rfl⟩
    have hprim := h_prim d hd
    apply primitive_divisor_is_factor hprim

  -- Now bound the cardinality
  rw [omega]
  calc (2^n - 1).primeFactors.card
      ≥ P.card := Finset.card_le_of_subset h_subset
    _ = S.attach.card := Finset.card_image_of_injOn (fun ⟨a, ha⟩ _ ⟨b, hb⟩ _ h => by
        simp only [Subtype.mk.injEq]
        apply h_inj a ha b hb h)
    _ = S.card := Finset.card_attach
    _ = ((n.divisors).filter (fun d => d ≠ 1 ∧ d ≠ 6)).card := rfl
    _ ≥ (n.divisors).card - 2 := by
      rw [tau, ← Finset.card_sdiff (s := n.divisors) (t := {1, 6})]
      · apply Nat.le_sub_of_add_le
        rw [add_comm]
        trans 2
        · exact Finset.card_le_two
        · rw [tsub_le_iff_right]
          have : S = n.divisors \ {1, 6} := by
            ext x
            simp only [S, mem_filter, mem_sdiff, mem_insert, mem_singleton, not_or]
          rw [this]
          rw [Finset.card_sdiff_eq_card_sub_card_inter]
          apply Nat.sub_le_sub_left
          trans ({1, 6} : Finset ℕ).card
          · apply Finset.card_le_card
            apply inter_subset_right
          · simp
      · intro x hx
        simp [S, mem_filter] at hx
        exact hx.1

lemma omega_pos_of_gt_one {n : ℕ} (h : n > 1) : omega n ≥ 1 := by
  rw [omega, Finset.card_pos, ← Finset.nonempty_iff_ne_empty]
  obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt h)
  use p
  rw [mem_primeFactors]
  refine ⟨hp.1, hp.2, Nat.ne_of_gt (Nat.lt_trans (by norm_num) h)⟩

/-- Mersenne instability: If a_k = 2^p - 1 is a Mersenne prime,
    then within 4 steps we reach a state with omega >= 2. -/
theorem mersenne_instability (p : ℕ) (hp : p.Prime) (h_mersenne : (2^p - 1).Prime) :
    let s := sigma 1
    let a := 2^p - 1
    let a1 := s a
    let a2 := s a1
    let a3 := s a2
    let a4 := s a3
    (omega a ≥ 2) ∨ (omega a1 ≥ 2) ∨ (omega a2 ≥ 2) ∨ (omega a3 ≥ 2) ∨ (omega a4 ≥ 2) := by
  let s := sigma 1
  let a := 2^p - 1
  let a1 := s a
  let a2 := s a1
  
  -- Calculate a1, a2
  have ha1 : a1 = 2^p := by
    dsimp [a1, s, a]
    rw [sigma_one_apply h_mersenne]
    ring
  
  have ha2 : a2 = 2^(p+1) - 1 := by
    dsimp [a2, s]
    rw [ha1]
    -- sigma 1 (2^p) = 2^(p+1) - 1
    rw [sigma_one_apply_prime_pow hp.two_le]
    simp
    ring
    rw [Nat.sub_one]
    simp
  
  by_cases p_eq_2 : p = 2
  · -- Case p=2
    subst p_eq_2
    simp [a2] at ha2
    -- ha2 says a2 = 7.
    let a3 := s a2
    let a4 := s a3
    have ha2_val : a2 = 7 := by rw [ha2]; norm_num
    have ha3 : a3 = 8 := by
      rw [ha2_val]
      dsimp [a3, s]
      rw [sigma_one_apply (by norm_num : Nat.Prime 7)]
    have ha4 : a4 = 15 := by
      rw [ha3]
      dsimp [a4, s]
      rw [sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
      norm_num
    
    right; right; right; right
    -- omega(15) = omega(3*5) = 2.
    rw [ha4, omega]
    have : (15 : ℕ).primeFactors = {3, 5} := by decide
    rw [this]
    simp
    
  · -- Case p > 2
    right; right; left
    -- omega a2 ≥ 2
    have p_odd : Odd p := hp.odd_of_ne_two p_eq_2
    obtain ⟨m, hm⟩ := p_odd
    -- p = 2*m + 1. Since p > 2, m ≥ 1.
    have m_ge_1 : m ≥ 1 := by
      have : p ≥ 3 := by
        rcases hp.eq_two_or_odd with rfl | _
        · contradiction
        · apply Nat.succ_le_of_lt
          apply Nat.lt_of_le_of_ne hp.two_le p_eq_2
      linarith
    
    have p_plus_1 : p + 1 = 2 * (m + 1) := by
      rw [hm]; ring
      
    let x := 2^(m+1)
    have ha2_split : a2 = (x - 1) * (x + 1) := by
      rw [ha2, p_plus_1, pow_mul, Nat.sq_sub_sq]
      simp
      
    have m_plus_1_ge_2 : m + 1 ≥ 2 := by linarith
    have x_ge_4 : x ≥ 4 := Nat.le_pow m_plus_1_ge_2 (by norm_num)
    
    have x_sub_1_pos : x - 1 > 1 := by linarith
    have x_add_1_pos : x + 1 > 1 := by linarith
    
    -- Coprime
    have h_coprime : Coprime (x - 1) (x + 1) := by
      rw [coprime_iff_gcd_eq_one]
      have : (x + 1) = (x - 1) + 2 := by omega
      rw [this, gcd_add_self_right]
      rw [Nat.gcd_comm]
      apply Nat.gcd_eq_one_left
      rw [← Nat.odd_iff_not_even]
      apply Even.sub_odd
      · exact even_pow.mpr ⟨even_two, Nat.ne_of_gt m_plus_1_ge_2⟩
      · exact odd_one
      
    rw [ha2_split]
    -- omega(a*b) = omega a + omega b if coprime a b
    rw [omega, primeFactors_mul (by linarith) (by linarith)]
    rw [Finset.card_union_of_disjoint]
    · have : omega (x - 1) ≥ 1 := omega_pos_of_gt_one x_sub_1_pos
      have : omega (x + 1) ≥ 1 := omega_pos_of_gt_one x_add_1_pos
      rw [omega] at *
      linarith
    · rw [Finset.disjoint_iff_ne]
      intro p hp q hq heq
      subst heq
      have : p ∣ gcd (x - 1) (x + 1) := dvd_gcd (mem_primeFactors.mp hp).2.1 (mem_primeFactors.mp hq).2.1
      rw [coprime_iff_gcd_eq_one.mp h_coprime] at this
      have : p ≠ 1 := (mem_primeFactors.mp hp).1.ne_one
      exact this (Nat.dvd_one.mp this)

end Erdos410
