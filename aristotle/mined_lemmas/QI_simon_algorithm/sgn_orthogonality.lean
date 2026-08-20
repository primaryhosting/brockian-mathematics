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

lemma sgn_orthogonality {n : ℕ} (y y' : Bits n) :
    ∑ x : Bits n, sgn x y * sgn x y' = if y = y' then (2:ℂ) ^ n else 0 := by
  have h : ∀ x : Bits n, sgn x y * sgn x y' = sgn x (y + y') := by
    intro x; rw [sgn_add_right]
  rw [Finset.sum_congr rfl (fun x _ => h x), sum_sgn]
  by_cases hyy : y = y'
  · subst hyy
    rw [if_pos rfl, if_pos (bits_add_self y)]
  · rw [if_neg hyy, if_neg]
    intro hc
    apply hyy
    have hc2 := congrArg (fun w => w + y') hc
    simp only [add_assoc, bits_add_self, add_zero, zero_add] at hc2
    exact hc2

/-- **The Hadamard layer is unitary**: it preserves the total squared amplitude. -/
