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

def qpt {n : ℕ} (A : ClassicalAlg n) (k : ℕ) : Bits n :=
  A.query (transcript A (fun x => x) k)

/-- The set of points queried in the first `q` rounds against the identity answers. -/
