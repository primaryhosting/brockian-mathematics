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

lemma bdot_eq_zero_iff {n : ℕ} (x : Bits n) : (∀ y, bdot x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have := h (Pi.single i 1)
    rwa [bdot_single] at this
  · rintro rfl y; simp

/-- Given a nonzero `s`, and `t` outside `{0, s}`, there is a vector orthogonal to `s`
but not to `t`. -/
