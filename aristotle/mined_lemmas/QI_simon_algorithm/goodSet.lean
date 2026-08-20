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

noncomputable def goodSet (n m : ℕ) (s : Bits n) : Finset (Fin m → Bits n) :=
  Finset.univ.filter (fun y => determines y s)

/-- The probability that `m` runs of Simon's algorithm determine the hidden shift. -/
