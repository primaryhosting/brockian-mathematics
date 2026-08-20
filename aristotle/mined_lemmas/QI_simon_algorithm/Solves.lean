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

def Solves {n : ℕ} (A : ClassicalAlg n) (q : ℕ) : Prop :=
  ∀ (f : Bits n → Bits n) (s : Bits n), SimonPromise f s → output A q f = s

/-- The `k`-th query point of the algorithm when all queries are answered by the identity. -/
