import Mathlib

namespace Brockian.MsPerronFrobenius

open Matrix Finset

/-- Probability vectors all of whose coordinates are at least `δ`. -/

lemma isCompact_Kset (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) : IsCompact (Kset n δ) := by
  -- Kset is a closed subset of the compact set [δ, 1]^n
  have hsub : Kset n δ ⊆ Set.Icc (fun _ : Fin n => δ) (fun _ => 1) := by
    intro x hx
    exact ⟨fun i => hx.1 i, fun i => Kset_le_one hδ hx i⟩
  have hclosed : IsClosed (Kset n δ) := by
    simp only [Kset]
    have h1 : IsClosed {x : Fin n → ℝ | ∀ i, δ ≤ x i} := by
      have : {x : Fin n → ℝ | ∀ i, δ ≤ x i} = ⋂ i : Fin n, {x | δ ≤ x i} := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le (continuous_const : Continuous (fun _ : Fin n → ℝ => δ)) (@continuous_apply (Fin n) (fun _ : Fin n => ℝ) _ i)
    have h2 : IsClosed {x : Fin n → ℝ | ∑ i, x i = 1} := by
      exact isClosed_eq (continuous_finset_sum _ fun i _ => @continuous_apply (Fin n) (fun _ : Fin n => ℝ) _ i) continuous_const
    exact h1.inter h2
  exact IsCompact.of_isClosed_subset (isCompact_Icc (α := Fin n → ℝ)) hclosed hsub

/-- The Collatz–Wielandt set: pairs `(t, x)` with `x` in `Kset n δ` and `t • x ≤ M x`. -/
