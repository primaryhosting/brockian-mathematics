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

noncomputable def measureTuple {n : ℕ} (m : ℕ) (f : Bits n → Bits n) (y : Fin m → Bits n) : ℝ :=
  ∑ z : Fin m → Bits n, Complex.normSq (tupleState m f (fun i => (y i, z i)))

