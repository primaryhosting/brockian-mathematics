import RequestProject.Degree

open Finset

namespace Frontier

/-! # Huang's sensitivity theorem: `s(f) ≥ √(deg f)`

Using the full-degree case `Frontier.huang_sensitivity` together with a restriction argument
to a subcube, we obtain the general statement: the sensitivity of a Boolean function is at
least the square root of its degree.
-/

section Coeff

variable {n : ℕ}

/-- Uniqueness of the multilinear representation. -/

lemma finrank_range_Bop (hn : 1 ≤ n) :
    2 ^ (n - 1) ≤ Module.finrank ℝ (LinearMap.range (Bop n)) := by
  have hcard : Module.finrank ℝ (Q n → ℝ) = 2 ^ n := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hle : Module.finrank ℝ ((LinearMap.range (Bop n) ⊔ LinearMap.range (Cop n) :
      Submodule ℝ (Q n → ℝ)))
      ≤ Module.finrank ℝ (LinearMap.range (Bop n)) + Module.finrank ℝ (LinearMap.range (Cop n)) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  rw [range_Bop_sup_range_Cop hn, finrank_range_Cop_eq_finrank_range_Bop] at hle
  rw [finrank_top, hcard] at hle
  have hpow : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  omega

/-- The subspace of vectors supported inside `S`. -/
