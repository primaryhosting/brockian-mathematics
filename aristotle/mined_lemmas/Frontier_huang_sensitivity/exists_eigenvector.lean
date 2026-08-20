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

lemma exists_eigenvector (hn : 1 ≤ n) (S : Finset (Q n)) (hS : 2 ^ (n - 1) < S.card) :
    ∃ v : Q n → ℝ, v ≠ 0 ∧ (∀ x, x ∉ S → v x = 0) ∧ hL n v = Real.sqrt n • v := by
  have hcard : Module.finrank ℝ (Q n → ℝ) = 2 ^ n := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hpow : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp [pow_succ]; ring
  set W : Submodule ℝ (Q n → ℝ) := suppSub S with hW
  set V : Submodule ℝ (Q n → ℝ) := LinearMap.range (Bop n) with hV
  have hWrank : Module.finrank ℝ W = S.card := finrank_suppSub S
  have hVrank : 2 ^ (n - 1) ≤ Module.finrank ℝ V := finrank_range_Bop hn
  have hsup : Module.finrank ℝ ((W ⊔ V : Submodule ℝ (Q n → ℝ))) ≤ 2 ^ n := by
    rw [← hcard]; exact Submodule.finrank_le _
  have hinf : Module.finrank ℝ ((W ⊔ V : Submodule ℝ (Q n → ℝ)))
      + Module.finrank ℝ ((W ⊓ V : Submodule ℝ (Q n → ℝ)))
      = Module.finrank ℝ W + Module.finrank ℝ V :=
    Submodule.finrank_sup_add_finrank_inf_eq W V
  have hpos : 0 < Module.finrank ℝ ((W ⊓ V : Submodule ℝ (Q n → ℝ))) := by omega
  have hne : (W ⊓ V : Submodule ℝ (Q n → ℝ)) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨v, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, ?_, ?_⟩
  · exact mem_suppSub.1 (Submodule.mem_inf.1 hvmem).1
  · obtain ⟨w, hw⟩ := (Submodule.mem_inf.1 hvmem).2
    rw [← hw]
    exact hL_Bop w

/-- Huang's theorem: any set of more than half of the vertices of the `n`-cube contains a
vertex with at least `√n` neighbours in the set. -/
