import RequestProject.Basic

/-!
# Covers, smallness, and Park–Pham minimum fragments
-/

namespace Math2

open Finset

variable {X : Type*} [DecidableEq X]

/-- `W` contains an edge of the hypergraph `H`, i.e. `W ∈ ⟨H⟩`. -/

lemma Exp_linear (V : Finset X) (c r s : ℝ) (F G : Finset X → ℝ) :
    Exp V c (fun W => r * F W + s * G W) = r * Exp V c F + s * Exp V c G := by
  unfold Exp
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => by ring

/-- Two independent rounds: the union of an `a`-random and a `b`-random subset is
`(a + b - a*b)`-random. -/
