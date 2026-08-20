import Mathlib
namespace Brockian.MsBirkhoff
/-- Birkhoff–von Neumann: every doubly stochastic matrix is a convex combination of permutation
    matrices. -/
theorem birkhoff_von_neumann {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hnn : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1) (hcol : ∀ j, ∑ i, M i j = 1) :
    ∃ (s : Finset (Equiv.Perm (Fin n))) (w : Equiv.Perm (Fin n) → ℝ),
      (∀ σ ∈ s, 0 ≤ w σ) ∧ (∑ σ ∈ s, w σ = 1) ∧
      M = ∑ σ ∈ s, w σ • (σ.permMatrix ℝ) := by
  sorry
end Brockian.MsBirkhoff
