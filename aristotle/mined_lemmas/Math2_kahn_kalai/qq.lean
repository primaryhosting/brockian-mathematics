import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

noncomputable def qq (L p : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => L * p + qq L p ((n + 1) / 2) - L * p * qq L p ((n + 1) / 2)

/-- The number of rounds used for an `ℓ`-bounded hypergraph. -/
