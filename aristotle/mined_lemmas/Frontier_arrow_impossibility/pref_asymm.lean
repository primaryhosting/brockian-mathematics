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

lemma pref_asymm (r : Ranking α) {x y : α} (h : r.pref x y) : ¬ r.pref y x := by
  rw [pref_iff_not_rel] at h ⊢
  intro h'
  exact h ((r.rel_total y x).resolve_right h')

