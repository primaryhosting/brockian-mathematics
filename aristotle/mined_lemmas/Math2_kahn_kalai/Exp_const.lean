import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_const (V : Finset X) (p : ℝ) (c : ℝ) : Exp V p (fun _ => c) = c := by
  unfold Exp
  rw [← Finset.sum_mul, sum_wt, one_mul]

