import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Aterm_nonneg {L : ℝ} (hL : 0 < L) (ℓ : ℕ) : 0 ≤ Aterm L ℓ := by
  unfold Aterm
  refine Finset.sum_nonneg fun m _ => ?_
  have : (0:ℝ) ≤ (1 / L) ^ m := by positivity
  positivity

