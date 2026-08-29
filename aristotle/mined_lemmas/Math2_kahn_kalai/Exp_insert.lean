import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_insert {V : Finset X} {x : X} (hx : x ∉ V) (p : ℝ) (f : Finset X → ℝ) :
    Exp (insert x V) p f
      = (1 - p) * Exp V p f + p * Exp V p (fun A => f (insert x A)) := by
  unfold Exp
  rw [Finset.sum_powerset_insert hx]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [wt_insert_of_notMem hx (Finset.mem_powerset.mp hA)]
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A hA => ?_)
    rw [wt_insert_of_mem hx (Finset.mem_powerset.mp hA)]
    ring

