import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Rankings -/

/-- A strict linear ranking (irreflexive, transitive, total) of the alternatives `A`.
`R.rel a b` means "`a` is strictly preferred to `b`". -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {a b c : A}, rel a b → rel b c → rel a c
  rel_irrefl : ∀ a : A, ¬ rel a a
  rel_total : ∀ a b : A, a ≠ b → rel a b ∨ rel b a

namespace Ranking

variable {A : Type*}


theorem exists_ne_two {e₁ e₂ e₃ : A} (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (p q : A) :
    ∃ z : A, z ≠ p ∧ z ≠ q := by
  rcases eq_or_ne e₁ p with rfl | h1
  · rcases eq_or_ne e₂ q with rfl | h2
    · exact ⟨e₃, Ne.symm h13, Ne.symm h23⟩
    · exact ⟨e₂, Ne.symm h12, h2⟩
  · rcases eq_or_ne e₁ q with rfl | hq
    · rcases eq_or_ne e₂ p with rfl | h2
      · exact ⟨e₃, Ne.symm h23, Ne.symm h13⟩
      · exact ⟨e₂, h2, Ne.symm h12⟩
    · exact ⟨e₁, h1, hq⟩

/-- Field expansion lemma: decisiveness over a single pair implies dictatorship. -/
