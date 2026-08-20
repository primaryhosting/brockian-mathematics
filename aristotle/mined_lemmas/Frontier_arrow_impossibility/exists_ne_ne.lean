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

theorem exists_ne_ne (h3 : ThreeAlternatives A) (p q : A) : ∃ d : A, d ≠ p ∧ d ≠ q := by
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := h3
  by_contra h
  push_neg at h
  have key : ∀ w : A, w = p ∨ w = q := by
    intro w
    rcases eq_or_ne w p with h' | h'
    · exact Or.inl h'
    · exact Or.inr (h w h')
  rcases key x with h1 | h1 <;> rcases key y with h2 | h2 <;> rcases key z with h3' | h3' <;>
    simp_all

/-- At least three alternatives, in terms of cardinality. -/
