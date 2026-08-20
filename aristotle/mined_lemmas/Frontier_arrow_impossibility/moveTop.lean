/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A ranked voting rule (social welfare function) turns a profile of individual rankings of the
alternatives into a social ranking.  Arrow's theorem says that as soon as there are at least
three alternatives, no such rule can be unanimous (Pareto), independent of irrelevant
alternatives, and non-dictatorial at the same time.

The key intermediate result is the *field expansion* / contagion lemma
`Frontier.decisive_of_almostDecisiveFor`: a coalition that gets its way on one ordered pair of
alternatives against unanimous opposition is decisive for *every* ordered pair.  A minimal
decisive coalition is then shown to be a singleton, i.e. a dictator.
-/

namespace Frontier

/-- A *ranking* of the alternatives `α`: a total, transitive, antisymmetric relation, i.e. a
linear order given as a relation.  `rel x y` reads "`x` is at least as good as `y`". -/
structure Ranking (α : Type*) where
  rel : α → α → Prop
  rel_total : ∀ x y, rel x y ∨ rel y x
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y

namespace Ranking

variable {α : Type*}

/-- Strict preference: `x` is ranked strictly above `y`. -/

def moveTop (b : α) (r : Ranking α) : Ranking α where
  rel x y := x = b ∨ (y ≠ b ∧ r.rel x y)
  rel_total x y := by
    by_cases hx : x = b
    · exact Or.inl (Or.inl hx)
    · by_cases hy : y = b
      · exact Or.inr (Or.inl hy)
      · rcases r.rel_total x y with h | h
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inr (Or.inr ⟨hx, h⟩)
  rel_trans := by
    rintro x y z (rfl | ⟨hy, hxy⟩) hyz
    · exact Or.inl rfl
    · rcases hyz with rfl | ⟨hz, hyz⟩
      · exact absurd rfl hy
      · exact Or.inr ⟨hz, r.rel_trans hxy hyz⟩
  rel_antisymm := by
    rintro x y (rfl | ⟨hy, hxy⟩) hyx
    · rcases hyx with rfl | ⟨hy, _⟩
      · rfl
      · exact absurd rfl hy
    · rcases hyx with rfl | ⟨_, hyx⟩
      · exact absurd rfl hy
      · exact r.rel_antisymm hxy hyx

