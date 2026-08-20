/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

lemma bdot_smul_right {n : ℕ} (a : ZMod 2) (x y : Bits n) :
    bdot x (a • y) = a * bdot x y := by
  simp only [bdot, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

