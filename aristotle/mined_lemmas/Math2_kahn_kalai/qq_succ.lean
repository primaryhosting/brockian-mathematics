import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma qq_succ (L p : ℝ) (n : ℕ) :
    qq L p (n + 1) = L * p + qq L p ((n + 1) / 2) - L * p * qq L p ((n + 1) / 2) := by
  rw [qq]

