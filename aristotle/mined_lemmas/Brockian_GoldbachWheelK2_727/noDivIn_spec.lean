import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib restatement

The target theorem `Brockian.GoldbachWheelK2_727` is stated in a self-contained way (its own
primality predicate `Brockian.IsPrime`), because the required file header must be the very first
thing in that file and Lean does not accept `import` after it.  Here we bridge that predicate to
`Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian


theorem noDivIn_spec (p : Nat) :
    ∀ k, noDivIn p k = true → ∀ m, 2 ≤ m → m ≤ k → p % m ≠ 0 := by
  intro k
  induction k with
  | zero => intro _ m hm hmk; omega
  | succ k ih =>
    match k with
    | 0 => intro _ m hm hmk; omega
    | k + 1 =>
      intro h m hm hmk
      rw [noDivIn] at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.lt_or_ge m (k + 2) with hlt | hge
      · exact ih h.2 m hm (by omega)
      · have hmeq : m = k + 2 := by omega
        subst hmeq
        exact h.1

/-- The Boolean test is sound. -/
