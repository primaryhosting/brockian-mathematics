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

theorem threeAlternatives_of_three_le_card [Fintype A] (h : 3 ≤ Fintype.card A) :
    ThreeAlternatives A := by
  have h' : 3 ≤ (Finset.univ : Finset A).card := by simpa using h
  obtain ⟨s, -, hcard⟩ := Finset.exists_subset_card_eq h'
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := Finset.card_eq_three.mp hcard
  exact ⟨x, y, z, hxy, hxz, hyz⟩

/-! ### The extremal lemma -/

/-- **Extremal lemma**: if in every voter's ranking `b` is either the best or the worst
alternative, then `b` is either socially best or socially worst. -/
