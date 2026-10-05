import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

def Exp (V : Finset X) (p : ℝ) (f : Finset X → ℝ) : ℝ := ∑ A ∈ V.powerset, wt V p A * f A

