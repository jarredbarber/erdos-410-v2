import Erdos.Helpers
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open ArithmeticFunction Filter

theorem erdos_410 : ∀ n > 1,
    Tendsto (fun k : ℕ ↦ ((sigma 1)^[k] n : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop atTop := by
  sorry
