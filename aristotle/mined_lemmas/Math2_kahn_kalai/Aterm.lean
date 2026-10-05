import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

noncomputable def Aterm (L : ℝ) (ℓ : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc (ℓ / 2 + 1) ℓ, 2 ^ ℓ * (1 / L) ^ m

/-- The bound on the total expected cost of the cover produced by the whole iteration. -/
