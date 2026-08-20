import Mathlib

/-!
# Preference relations for Arrow's impossibility theorem

`Pref A` is a weak preference relation on the set of alternatives `A`: a total preorder,
where `r.le a b` means "`b` is at least as good as `a`" (higher is better).

`LinPref A` is a *ranking*: a weak preference with no ties (an antisymmetric total preorder,
i.e. a linear order).

This file develops the basic API together with the constructions of rankings that are used
in the proof of Arrow's theorem.
-/

open scoped Classical

namespace Frontier

/-- A weak preference relation on `A`: a total preorder.
`r.le a b` means "`b` is at least as good as `a`". -/
structure Pref (A : Type*) where
  /-- `le a b` means "`b` is at least as good as `a`". -/
  le : A → A → Prop
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c : A}, le a b → le b c → le a c
  le_total : ∀ a b, le a b ∨ le b a

/-- A ranking of the alternatives: a weak preference with no ties. -/
structure LinPref (A : Type*) extends Pref A where
  le_antisymm : ∀ {a b : A}, le a b → le b a → a = b

namespace Pref

variable {A : Type*} (r : Pref A)

/-- Strict preference: `r.lt a b` means "`b` is strictly better than `a`". -/

theorem midPref_le_of_ne (r : LinPref A) {b a x y : A} (hx : x ≠ b) (hy : y ≠ b) :
    (r.midPref b a).le x y ↔ r.le x y := by
  simp only [midPref, lex_le, if_neg hx, if_neg hy]
  by_cases hax : r.le a x <;> by_cases hay : r.le a y <;>
    simp only [hax, hay, if_true, if_false]
  · simp
  · exact iff_of_false (by simp) (fun h => hay (r.le_trans hax h))
  · exact iff_of_true (Or.inl (by omega)) (r.le_trans ((r.le_total a x).resolve_left hax) hay)
  · simp

/-- In `r.midPref b a`, the alternative `a` is strictly better than `b`. -/
