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

lemma conj_sgn {n : ℕ} (x y : Bits n) : (starRingEnd ℂ) (sgn x y) = sgn x y := by
  simp only [sgn]
  split <;> simp

/-- A (pure) state of the two `n`-qubit registers used by Simon's algorithm, given by its
amplitudes in the computational basis. -/
abbrev Amp (n : ℕ) : Type := Bits n × Bits n → ℂ

/-- The all-zero computational basis state. -/
