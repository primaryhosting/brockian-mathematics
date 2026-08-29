import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

noncomputable def coverFam (H : Finset (Finset X)) (W : Finset X) (m₀ : ℕ) :
    Finset (Finset X) :=
  (bigFam H W m₀).image (fun S => frag H W S)

/-- The hypergraph carried to the next round. -/
