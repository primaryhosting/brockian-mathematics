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

lemma sqrt_two_pow_ne_zero (n : ℕ) : ((Real.sqrt (2 ^ n) : ℝ) : ℂ) ≠ 0 := by
  have h : (0:ℝ) < Real.sqrt (2 ^ n) := Real.sqrt_pos.2 (by positivity)
  exact_mod_cast h.ne'

