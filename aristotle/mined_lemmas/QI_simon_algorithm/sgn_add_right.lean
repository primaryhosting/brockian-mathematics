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

lemma sgn_add_right {n : ℕ} (x y y' : Bits n) : sgn x (y + y') = sgn x y * sgn x y' := by
  rw [sgn_comm, sgn_add_left, sgn_comm y x, sgn_comm y' x]

/-- The sum of a nontrivial character over the group of bit strings vanishes. -/
