import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

noncomputable def Bb (L : ℝ) : ℕ → ℝ
  | 0 => 0
  | (n + 1) => Aterm L (n + 1) + Bb L ((n + 1) / 2)

