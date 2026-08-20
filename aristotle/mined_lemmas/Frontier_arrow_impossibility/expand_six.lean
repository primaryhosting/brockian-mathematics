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

lemma expand_six (hU : Unanimous F) (hI : IIA F) {G : Finset V} {a b c : α}
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) (h : AlmostDecisiveFor F G a b) :
    AlmostDecisiveFor F G a c ∧ AlmostDecisiveFor F G c b ∧ AlmostDecisiveFor F G b c ∧
      AlmostDecisiveFor F G c a ∧ AlmostDecisiveFor F G b a := by
  have hac : AlmostDecisiveFor F G a c :=
    AlmostDecisiveFor_of_DecisiveFor (expand_right hU hI hab hca hcb h)
  have hcb' : AlmostDecisiveFor F G c b :=
    AlmostDecisiveFor_of_DecisiveFor (expand_left hU hI hab hca hcb h)
  have hbc : AlmostDecisiveFor F G b c :=
    AlmostDecisiveFor_of_DecisiveFor
      (expand_left hU hI (Ne.symm hca) (Ne.symm hab) (Ne.symm hcb) hac)
  have hca' : AlmostDecisiveFor F G c a :=
    AlmostDecisiveFor_of_DecisiveFor (expand_right hU hI hcb (Ne.symm hca) hab hcb')
  have hba : AlmostDecisiveFor F G b a :=
    AlmostDecisiveFor_of_DecisiveFor
      (expand_right hU hI (Ne.symm hcb) hab (Ne.symm hca) hbc)
  exact ⟨hac, hcb', hbc, hca', hba⟩

/-- **Contagion / field expansion lemma.**  A coalition that is almost decisive for a single
ordered pair of distinct alternatives is decisive for every ordered pair. -/
