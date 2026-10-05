import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Bb_succ (L : ℝ) (n : ℕ) : Bb L (n + 1) = Aterm L (n + 1) + Bb L ((n + 1) / 2) := by
  rw [Bb]

