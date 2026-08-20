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

lemma sgn_add_left {n : ℕ} (x x' y : Bits n) : sgn (x + x') y = sgn x y * sgn x' y := by
  simp only [sgn, bdot_add_left]
  rcases zmod_two_cases (bdot x y) with h | h <;> rcases zmod_two_cases (bdot x' y) with h' | h' <;>
      rw [h, h']
  · norm_num
  · rw [if_neg (show ¬ ((0 : ZMod 2) + 1 = 0) from by decide), if_pos rfl,
      if_neg (show ¬ ((1 : ZMod 2) = 0) from by decide)]
    norm_num
  · rw [if_neg (show ¬ ((1 : ZMod 2) + 0 = 0) from by decide), if_pos rfl,
      if_neg (show ¬ ((1 : ZMod 2) = 0) from by decide)]
    norm_num
  · rw [if_pos (show (1 : ZMod 2) + 1 = 0 from by decide),
      if_neg (show ¬ ((1 : ZMod 2) = 0) from by decide)]
    norm_num

