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

theorem initState_normSq_sum (n : ℕ) :
    ∑ p : Bits n × Bits n, Complex.normSq (initState n p) = 1 := by
  classical
  rw [Finset.sum_eq_single ((0 : Bits n), (0 : Bits n))]
  · simp [initState]
  · intro b _ hb
    simp [initState, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **One quantum query suffices to sample uniformly from `s^⊥`.**  Measuring the first
register after one iteration of Simon's algorithm yields a uniformly random element of the
hyperplane orthogonal to the hidden shift `s`. -/
