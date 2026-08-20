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

theorem lex_lt {r : LinPref A} {f : A → ℕ} {a b : A} :
    (r.lex f).lt a b ↔ (f a < f b ∨ (f a = f b ∧ r.lt a b)) := by
  simp only [Pref.lt, lex_le, not_or, not_and]
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases lt_trichotomy (f a) (f b) with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', h₂ h'.symm⟩
    · exact absurd h' (by omega)
  · rintro (h | ⟨h, h'⟩)
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, fun _ => h'⟩

/-- Precomposition of a ranking with a permutation of the alternatives. -/
