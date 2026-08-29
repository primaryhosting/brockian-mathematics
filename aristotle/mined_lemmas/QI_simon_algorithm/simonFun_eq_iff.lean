/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced above as a plain block comment: Lean 4 does not allow a
-- module docstring `/-! ... -/` to precede the `import` lines.)

import Mathlib

/-!
## Simon's problem

Simon's problem: a function `f` on `n`-bit strings is promised to be two-to-one with
`f x = f y ↔ y = x ∨ y = x + s` for a hidden nonzero secret `s`; the task is to find `s`.

This file formalises the two information-theoretic facts behind the statement
"Simon's problem takes `O(n)` quantum queries but `Ω(2^(n/2))` classical queries":

* **Quantum side.** Each run of Simon's quantum subroutine returns a uniformly random
  vector `y` in the hyperplane `s^⊥`. We show that `n` such vectors always suffice:
  for every nonzero `s` there is a set `Y` of at most `n` vectors orthogonal to `s`
  such that `s` is the unique nonzero vector orthogonal to all of `Y`. Hence `O(n)`
  quantum queries pin down the secret.

* **Classical side.** A classical algorithm only learns something about `s` when two of
  its queries collide. We show that a query set `Q` that is guaranteed to contain a
  collision for *every* possible secret must satisfy `2 ^ n ≤ Q.card ^ 2`, i.e.
  `Q.card ≥ 2 ^ (n / 2)`. Moreover, if `Q.card ^ 2 + 3 ≤ 2 ^ n`, then there are two
  *different* secrets whose Simon functions agree on `Q` up to a global relabelling of
  the output values, so no classical algorithm making those queries can tell them apart.
-/

namespace QI

open Finset

/-- `n`-bit strings, viewed as vectors over the field with two elements. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The mod-2 inner product of two bit strings. -/

theorem simonFun_eq_iff {n : ℕ} {s : Bits n} {j : Fin n} (hsj : s j = 1) (x y : Bits n) :
    simonFun s j x = simonFun s j y ↔ (y = x ∨ y = x + s) := by
  constructor
  · intro h
    have h' : ∀ i, x i + x j * s i = y i + y j * s i := fun i => congrFun h i
    by_cases hj : x j = y j
    · left
      funext i
      have hi := h' i
      rw [hj] at hi
      exact (add_right_cancel hi).symm
    · right
      have hyj : y j = x j + 1 := zmod2_ne_iff hj
      funext i
      have hi := h' i
      rw [hyj] at hi
      simp only [Pi.add_apply]
      revert hi
      generalize x i = a
      generalize y i = b
      generalize x j = c
      generalize s i = d
      revert a b c d
      decide
  · rintro (rfl | rfl)
    · rfl
    · funext i
      show x i + x j * s i = (x + s) i + (x + s) j * s i
      simp only [Pi.add_apply, hsj]
      rw [zmod2_add_mul]

/-! ### Quantum side: `n` measurement outcomes determine the secret -/

/-- Given a nonzero secret `s`, there is a set `Y` of at most `n` vectors, all orthogonal to
`s`, such that `s` is the only nonzero vector orthogonal to every element of `Y`.
Since Simon's quantum subroutine returns uniformly random elements of `s^⊥`, this says that
`O(n)` quantum queries suffice to determine `s`. -/
