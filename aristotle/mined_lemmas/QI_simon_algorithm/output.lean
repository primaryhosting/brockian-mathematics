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

def output {n : ℕ} (A : ClassicalAlg n) (q : ℕ) (f : Bits n → Bits n) : Bits n :=
  A.out (transcript A f q)

/-- The algorithm solves Simon's problem with `q` queries. -/
