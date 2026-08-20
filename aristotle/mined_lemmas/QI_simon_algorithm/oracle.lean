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

def oracle {n : ℕ} (f : Bits n → Bits n) (psi : Amp n) : Amp n :=
  fun p => psi (p.1, p.2 - f p.1)

/-- The state produced by one iteration of Simon's algorithm: Hadamard, one query, Hadamard. -/
