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

theorem isDictator_of_decisiveOff {F : SWF V A} (hU : Unanimity F)
    (h3 : ThreeAlternatives A) (hdec : ∀ b : A, ∃ i : V, DecisiveOff F i b)
    {b : A} {i : V} (hi : DecisiveOff F i b) : IsDictator F i := by
  intro P x y hxy
  by_cases hb : x ≠ b ∧ y ≠ b
  · exact hi P x y hb.1 hb.2 hxy
  · obtain ⟨c, hcx, hcy⟩ := exists_ne_ne h3 x y
    have hcb : c ≠ b := by
      rcases not_and_or.mp hb with h | h
      · rw [not_not] at h; rw [← h]; exact hcx
      · rw [not_not] at h; rw [← h]; exact hcy
    obtain ⟨j, hj⟩ := hdec c
    have hij : i = j := decisiveOff_unique hU h3 (Ne.symm hcb) hi hj
    subst hij
    exact hj P x y (Ne.symm hcx) (Ne.symm hcy) hxy

/-! ### Arrow's theorem -/

/-- Arrow's theorem for `n > 0` voters indexed by `Fin n`: unanimity and IIA force a dictator. -/
