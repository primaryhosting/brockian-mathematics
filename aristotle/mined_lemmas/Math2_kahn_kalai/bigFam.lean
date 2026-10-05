import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

noncomputable def bigFam (H : Finset (Finset X)) (W : Finset X) (m₀ : ℕ) : Finset (Finset X) :=
  H.filter (fun S => m₀ < (frag H W S).card)

/-- The cover produced in one round. -/
