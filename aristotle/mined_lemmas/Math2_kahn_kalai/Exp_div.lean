import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_div (V : Finset X) (p : ℝ) (f : Finset X → ℝ) (c : ℝ) :
    Exp V p (fun A => f A / c) = Exp V p f / c := by
  unfold Exp
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun A _ => by ring)

