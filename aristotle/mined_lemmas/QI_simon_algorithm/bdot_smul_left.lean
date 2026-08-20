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

lemma bdot_smul_left {n : ℕ} (a : ZMod 2) (x y : Bits n) :
    bdot (a • x) y = a * bdot x y := by
  rw [bdot_comm, bdot_smul_right, bdot_comm]

/-- Evaluating the pairing against a standard basis vector. -/
