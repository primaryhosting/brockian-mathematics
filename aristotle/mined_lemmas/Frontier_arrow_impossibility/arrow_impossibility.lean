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

theorem arrow_impossibility {V α : Type*} [Fintype V] (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (F : (V → Ranking α) → Ranking α) :
    ¬ (Unanimous F ∧ IIA F ∧ ∀ i : V, ¬ IsDictator F i) := by
  rintro ⟨hU, hI, hnd⟩
  obtain ⟨i, hi⟩ := exists_dictator hU hI a b c hab hac hbc
  exact hnd i hi

/-- Non-vacuity check: dropping non-dictatorship the axioms *are* satisfiable — the projection
onto voter `i` (the dictatorship of `i`) is unanimous, satisfies IIA, and has `i` as a
dictator. -/
