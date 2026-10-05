import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_sum {ι : Type*} (V : Finset X) (p : ℝ) (s : Finset ι) (f : ι → Finset X → ℝ) :
    Exp V p (fun A => ∑ i ∈ s, f i A) = ∑ i ∈ s, Exp V p (f i) := by
  simp only [Exp, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- A chosen edge of `H` inside `Z`, when there is one. -/
