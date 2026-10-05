import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_add (V : Finset X) (p : ℝ) (f g : Finset X → ℝ) :
    Exp V p (fun A => f A + g A) = Exp V p f + Exp V p g := by
  unfold Exp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun A _ => by ring)

