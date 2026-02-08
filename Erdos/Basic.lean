import Erdos.Helpers
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto

open ArithmeticFunction Filter Erdos410

/-! ## Intermediate lemmas for the Erdős #410 proof

The proof follows the assembly in proofs/main-assembly-v2.md:
1. Ratio divergence: σ₁(aₖ)/aₖ → ∞ (sorry — NL proof not yet verified)
2. Geometric growth: for any C > 1, eventually aₖ₊₁ ≥ C · aₖ, giving aₖ ≥ C^j · a_K
3. Exponential bound: aₖ ≥ C^k for large k
4. k-th root: aₖ^{1/k} ≥ C for large k
5. Main theorem: aₖ^{1/k} → ∞
-/

namespace Erdos410Assembly

/-- The iterate σ₁^[k](n) is at least 2 when n ≥ 2. -/
lemma iterate_ge_two (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : 2 ≤ (sigma 1)^[k] n := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq]; exact hn
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have := sigma_one_ge ((sigma 1)^[k] n) ih
    omega

/-- The iterate σ₁^[k](n) is at least n + k when n ≥ 2. -/
lemma iterate_ge_add (n : ℕ) (hn : 2 ≤ n) (k : ℕ) : n + k ≤ (sigma 1)^[k] n := by
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.add_zero, le_refl]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hge2 : 2 ≤ (sigma 1)^[k] n := iterate_ge_two n hn k
    have := sigma_one_ge ((sigma 1)^[k] n) hge2
    omega

/-- The iterate σ₁^[k](n) cast to ℝ is positive when n ≥ 2. -/
lemma iterate_cast_pos (n : ℕ) (hn : 2 ≤ n) (k : ℕ) :
    (0 : ℝ) < ((sigma 1)^[k] n : ℝ) := by
  exact Nat.cast_pos.mpr (by have := iterate_ge_two n hn k; omega)

/-- **Ratio divergence** along the orbit σ₁^[k](n).

This is the key unproved lemma. The NL proof in proofs/ratio-divergence.md
was Rejected ❌ and needs a new approach.

Statement: for n ≥ 2, the ratio σ₁(aₖ)/aₖ tends to +∞. -/
lemma ratio_divergence (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun k ↦ (((sigma 1)^[k + 1] n : ℕ) : ℝ) / ((sigma 1)^[k] n : ℝ))
      atTop atTop := by
  sorry

/-- From ratio divergence: for any C > 0, eventually σ₁(aₖ) ≥ C · aₖ.

Proof: ratio divergence gives σ₁(aₖ)/aₖ → ∞, so eventually the ratio ≥ C.
Multiply through (aₖ > 0) to get σ₁(aₖ) ≥ C · aₖ. -/
lemma eventually_ratio_ge (n : ℕ) (hn : 2 ≤ n) (C : ℝ) :
    ∃ K, ∀ k, K ≤ k →
      C * ((sigma 1)^[k] n : ℝ) ≤ ((sigma 1)^[k + 1] n : ℝ) := by
  have hrd := ratio_divergence n hn
  rw [tendsto_atTop_atTop] at hrd
  obtain ⟨K, hK⟩ := hrd C
  exact ⟨K, fun k hk => by
    have hak_pos := iterate_cast_pos n hn k
    have := hK k hk
    rwa [le_div_iff₀ hak_pos] at this⟩

/-- Geometric growth past the threshold: once the ratio exceeds C for all k ≥ K,
the iterates grow geometrically: a_{K+j} ≥ C^j · a_K.

This is Step 2 of the assembly proof (induction on j). -/
lemma geometric_growth (n : ℕ) (hn : 2 ≤ n) (C : ℝ) (hC : 0 < C) :
    ∃ K : ℕ, ∀ j : ℕ,
      C ^ j * ((sigma 1)^[K] n : ℝ) ≤ ((sigma 1)^[K + j] n : ℝ) := by
  obtain ⟨K, hK⟩ := eventually_ratio_ge n hn C
  exact ⟨K, fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show K + (j + 1) = (K + j) + 1 from by ring]
      have hKj : K ≤ K + j := Nat.le_add_right K j
      calc C ^ (j + 1) * ((sigma 1)^[K] n : ℝ)
          = C * (C ^ j * ((sigma 1)^[K] n : ℝ)) := by ring
        _ ≤ C * ((sigma 1)^[K + j] n : ℝ) := by
            exact mul_le_mul_of_nonneg_left ih (le_of_lt hC)
        _ ≤ ((sigma 1)^[(K + j) + 1] n : ℝ) := hK (K + j) hKj⟩

/-- For any C > 1, eventually σ₁^[k](n) ≥ C^k (as reals).

This combines geometric_growth with the fact that a_K ≥ 1:
Use geometric growth with C² to get a_{K+j} ≥ (C²)^j · a_K.
For k ≥ 2K: j = k-K ≥ K so 2j ≥ k, giving (C²)^j ≥ C^k.
Also a_K ≥ 1, so a_k ≥ C^k.
This is Steps 2-3 of the assembly proof. -/
lemma eventually_exponential_bound (n : ℕ) (hn : 2 ≤ n) (C : ℝ) (hC : 1 < C) :
    ∃ N : ℕ, ∀ k, N ≤ k → C ^ k ≤ ((sigma 1)^[k] n : ℝ) := by
  -- Use geometric_growth with C² (which is > 0 since C > 1 > 0)
  have hC2 : 0 < C ^ 2 := by positivity
  obtain ⟨K, hK⟩ := geometric_growth n hn (C ^ 2) hC2
  -- For k ≥ 2*K, we have j = k - K and 2*j ≥ k
  use 2 * K
  intro k hk
  -- Write k = K + j where j = k - K
  have hKk : K ≤ k := by omega
  set j := k - K with hj_def
  have hkKj : k = K + j := by omega
  -- Key: (C²)^j ≥ C^k because 2j ≥ k
  have h2j : k ≤ 2 * j := by omega
  have hCge1 : 1 ≤ C := le_of_lt hC
  have hC_pos : 0 < C := by linarith
  have hCk_le_C2j : C ^ k ≤ (C ^ 2) ^ j := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hCge1 h2j
  -- Also a_K ≥ 2, so (a_K : ℝ) ≥ 1
  have haK_ge : (1 : ℝ) ≤ ((sigma 1)^[K] n : ℝ) := by
    have := iterate_ge_two n hn K
    exact le_of_lt (by exact_mod_cast (by omega : 1 < (sigma 1)^[K] n))
  -- Combine: C^k ≤ (C²)^j ≤ (C²)^j * a_K ≤ a_{K+j} = a_k
  calc C ^ k
      ≤ (C ^ 2) ^ j := hCk_le_C2j
    _ ≤ (C ^ 2) ^ j * ((sigma 1)^[K] n : ℝ) := le_mul_of_one_le_right (by positivity) haK_ge
    _ ≤ ((sigma 1)^[K + j] n : ℝ) := hK j
    _ = ((sigma 1)^[k] n : ℝ) := by rw [hkKj]

/-- If C^k ≤ aₖ (as reals) with C > 0, aₖ > 0, k ≥ 1, then C ≤ aₖ^{1/k}.

This is the key rpow step (Step 3 of the assembly). -/
lemma rpow_kth_root_ge {C : ℝ} {a : ℝ} {k : ℕ} (hC : 0 < C) (_ha : 0 ≤ a)
    (hk : k ≠ 0) (h : C ^ k ≤ a) :
    C ≤ a ^ ((1 : ℝ) / (k : ℝ)) := by
  calc C = (C ^ k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
        rw [show (1 : ℝ) / (k : ℝ) = (↑k)⁻¹ from one_div (k : ℝ)]
        rw [← Real.rpow_natCast C k, ← Real.rpow_mul (le_of_lt hC)]
        simp [Nat.cast_ne_zero.mpr hk]
    _ ≤ a ^ ((1 : ℝ) / (k : ℝ)) := by
        apply Real.rpow_le_rpow (by positivity) h
        positivity

/-- For n ≥ 2, for any C > 1, eventually σ₁^[k](n)^{1/k} ≥ C.

This is Step 4 of the assembly proof: combine the exponential bound with the
k-th root extraction. -/
lemma kth_root_eventually_ge (n : ℕ) (hn : 2 ≤ n) (C : ℝ) (hC : 1 < C) :
    ∀ᶠ k in atTop, C ≤ ((sigma 1)^[k] n : ℝ) ^ ((1 : ℝ) / (k : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_exponential_bound n hn C hC
  rw [Filter.eventually_atTop]
  -- For k ≥ max N 1, we have C^k ≤ a_k and k ≥ 1
  exact ⟨max N 1, fun k hk => by
    have hkN : N ≤ k := le_of_max_le_left hk
    have hk1 : 1 ≤ k := le_of_max_le_right hk
    have hk_ne : k ≠ 0 := by omega
    exact rpow_kth_root_ge (by linarith) (by positivity) hk_ne (hN k hkN)⟩

end Erdos410Assembly

/-- **Erdős Problem #410**: For n > 1, the sequence σ₁^[k](n)^{1/k} → ∞.

The proof reduces to showing that the ratio σ₁(aₖ)/aₖ → ∞ along the orbit
(ratio_divergence, currently sorry). Given this, the assembly argument shows:
- For any C > 1, eventually aₖ ≥ C^k (geometric growth)
- Therefore aₖ^{1/k} ≥ C for large k
- Since C was arbitrary, aₖ^{1/k} → ∞

The only sorry is in ratio_divergence (proofs/ratio-divergence.md needs revision).
-/
theorem erdos_410 : ∀ n > 1,
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop atTop := by
  intro n hn
  have hn2 : 2 ≤ n := hn
  rw [Filter.tendsto_atTop_atTop]
  intro b
  -- For any bound b, pick C = max b 2 (so C > 1)
  -- Then by kth_root_eventually_ge, eventually a_k^{1/k} ≥ C ≥ b
  have hC : (1 : ℝ) < max b 2 := by simp only [lt_max_iff]; right; norm_num
  have key := Erdos410Assembly.kth_root_eventually_ge n hn2 (max b 2) hC
  rw [Filter.eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  exact ⟨N, fun k hk => le_trans (le_max_left b 2) (hN k hk)⟩
