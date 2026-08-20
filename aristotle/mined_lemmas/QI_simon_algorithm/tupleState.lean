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

noncomputable def tupleState {n : ℕ} (m : ℕ) (f : Bits n → Bits n) :
    (Fin m → Bits n × Bits n) → ℂ := fun v => ∏ i, simonState f (v i)

/-- Probability of observing the tuple `y` of outcomes when measuring the first register of
each of the `m` copies. -/
