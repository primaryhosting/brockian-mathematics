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

theorem exists_dictator_fin {n : ℕ} (hn : 0 < n) (h3 : ThreeAlternatives A)
    {F : SWF (Fin n) A} (hU : Unanimity F) (hI : IIA F) : ∃ i : Fin n, IsDictator F i := by
  obtain ⟨x, -, -, -, -, -⟩ := id h3
  have hdec : ∀ b : A, ∃ i : Fin n, DecisiveOff F i b := fun b =>
    exists_decisiveOff hn h3 hU hI b
  obtain ⟨i, hi⟩ := hdec x
  exact ⟨i, isDictator_of_decisiveOff hU h3 hdec hi⟩

/-- **Arrow's theorem**: for a finite nonempty set of voters and at least three alternatives,
every social welfare function satisfying unanimity and independence of irrelevant alternatives
has a dictator. -/
