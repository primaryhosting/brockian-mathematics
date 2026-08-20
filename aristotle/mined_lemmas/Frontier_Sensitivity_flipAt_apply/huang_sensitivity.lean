import Mathlib
open Finset Matrix
namespace Frontier.Sensitivity

/-- Vertices of the n-dimensional Boolean hypercube. -/
abbrev Q (n : ℕ) := Fin n → Bool

/-- Two vertices are adjacent iff they differ in exactly one coordinate. -/

theorem huang_sensitivity {n : ℕ} (hn : 0 < n) (H : Finset (Q n))
    (hH : 2 ^ (n - 1) + 1 ≤ H.card) :
    ∃ v ∈ H, Real.sqrt n ≤ (degIn H v : ℝ) := by
  -- the two eigenspaces together span the whole space, so one of them is big
  have hsup := eigsp_sup_eigsp (n := n) hn
  have hdim : 2 ^ n ≤ Module.finrank ℝ (eigsp (n := n) (Real.sqrt n))
      + Module.finrank ℝ (eigsp (n := n) (-Real.sqrt n)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (eigsp (n := n) (Real.sqrt n)) (eigsp (n := n) (-Real.sqrt n))
    rw [hsup, finrank_top, finrank_pi_cube] at h
    omega
  have hhalf : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
    simp [pow_succ]
    ring
  -- pick an eigenvalue whose eigenspace has dimension at least `2 ^ (n-1)`
  obtain ⟨c, hc, hcdim⟩ : ∃ c : ℝ, |c| = Real.sqrt n ∧
      2 ^ (n - 1) ≤ Module.finrank ℝ (eigsp (n := n) c) := by
    have hnn : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    by_cases h : 2 ^ (n - 1) ≤ Module.finrank ℝ (eigsp (n := n) (Real.sqrt n))
    · exact ⟨Real.sqrt n, abs_of_nonneg hnn, h⟩
    · exact ⟨-Real.sqrt n, by rw [abs_neg, abs_of_nonneg hnn], by omega⟩
  -- intersect with the space of vectors supported on `H`
  have hW := finrank_suppSpace H
  have hinf := Submodule.finrank_sup_add_finrank_inf_eq (eigsp (n := n) c) (suppSpace H)
  have hsupple : Module.finrank ℝ ((eigsp (n := n) c) ⊔ (suppSpace H) : Submodule ℝ (Q n → ℝ))
      ≤ 2 ^ n := by
    have h := Submodule.finrank_le ((eigsp (n := n) c) ⊔ (suppSpace H))
    rwa [finrank_pi_cube] at h
  have hpos : 0 < Module.finrank ℝ ((eigsp (n := n) c) ⊓ (suppSpace H) : Submodule ℝ (Q n → ℝ)) := by
    omega
  have hne : ((eigsp (n := n) c) ⊓ (suppSpace H) : Submodule ℝ (Q n → ℝ)) ≠ ⊥ := by
    intro h
    rw [h] at hpos
    simp at hpos
  obtain ⟨y, hymem, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hymem
  exact exists_large_degree_of_eigenvector H c hc y hy0
    ((mem_eigsp_iff c y).1 hymem.1) ((mem_suppSpace_iff H y).1 hymem.2)

end Frontier.Sensitivity

