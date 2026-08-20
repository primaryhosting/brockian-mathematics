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

noncomputable def measureFst {n : ℕ} (psi : Amp n) (y : Bits n) : ℝ :=
  ∑ z, Complex.normSq (psi (y, z))

/-- Simon's promise: `f` is invariant under the shift `s ≠ 0` and otherwise injective. -/
