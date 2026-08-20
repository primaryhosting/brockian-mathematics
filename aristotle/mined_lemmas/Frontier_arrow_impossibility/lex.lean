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

def lex (r : LinPref A) (f : A → ℕ) : LinPref A where
  le a b := f a < f b ∨ (f a = f b ∧ r.le a b)
  le_refl a := Or.inr ⟨rfl, r.le_refl a⟩
  le_trans := by
    rintro a b c (h₁ | ⟨h₁, h₁'⟩) (h₂ | ⟨h₂, h₂'⟩)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, r.le_trans h₁' h₂'⟩
  le_total a b := by
    rcases lt_trichotomy (f a) (f b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases r.le_total a b with h' | h'
      · exact Or.inl (Or.inr ⟨h, h'⟩)
      · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
    · exact Or.inr (Or.inl h)
  le_antisymm := by
    rintro a b (h₁ | ⟨h₁, h₁'⟩) (h₂ | ⟨h₂, h₂'⟩)
    · omega
    · omega
    · omega
    · exact r.le_antisymm h₁' h₂'

