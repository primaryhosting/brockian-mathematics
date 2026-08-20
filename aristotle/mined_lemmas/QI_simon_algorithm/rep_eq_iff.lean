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

lemma rep_eq_iff (s : Bits n) (j : Fin n) (hj : s j = 1) (x y : Bits n) :
    rep s j x = rep s j y ↔ (y = x ∨ y = x + s) := by
  have hadd : ∀ w : Bits n, (w + s) j = w j + 1 := by
    intro w; simp [hj]
  have hcancel : ∀ a b : Bits n, a + s = b + s ↔ a = b := by
    intro a b
    constructor
    · intro h
      have := congrArg (fun w => w + s) h
      simpa [add_assoc, bits_add_self] using this
    · intro h; rw [h]
  have hshift : ∀ a b : Bits n, a = b + s ↔ b = a + s := by
    intro a b
    constructor <;> intro h <;> rw [h] <;> simp [add_assoc, bits_add_self]
  rcases zmod_two_cases (x j) with hx | hx <;> rcases zmod_two_cases (y j) with hy | hy
  · rw [rep, rep, if_pos hx, if_pos hy]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | h)
      · exact h.symm
      · exfalso
        rw [h, hadd, hx] at hy
        exact absurd hy (by decide)
  · rw [rep, rep, if_pos hx, if_neg (by rw [hy]; decide)]
    constructor
    · intro h
      exact Or.inr ((hshift x y).1 h)
    · rintro (h | h)
      · exfalso
        rw [h, hx] at hy
        exact absurd hy (by decide)
      · rw [h]
        rw [add_assoc, bits_add_self, add_zero]
  · rw [rep, rep, if_neg (by rw [hx]; decide), if_pos hy]
    constructor
    · intro h
      exact Or.inr h.symm
    · rintro (h | h)
      · exfalso
        rw [h, hx] at hy
        exact absurd hy (by decide)
      · exact h.symm
  · rw [rep, rep, if_neg (by rw [hx]; decide), if_neg (by rw [hy]; decide), hcancel]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | h)
      · exact h.symm
      · exfalso
        rw [h, hadd, hx] at hy
        exact absurd hy (by decide)

/-- A Simon function with hidden shift `s` fixing all the queried points. -/
