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

lemma decisive_of_almostDecisiveFor (hU : Unanimous F) (hI : IIA F)
    (h3 : ∀ x y : α, ∃ z : α, z ≠ x ∧ z ≠ y) {G : Finset V} {a b : α}
    (hab : a ≠ b) (h : AlmostDecisiveFor F G a b) : Decisive F G := by
  intro x y hxy
  have key : AlmostDecisiveFor F G x y := by
    by_cases hxa : x = a
    · by_cases hyb : y = b
      · rw [hxa, hyb]; exact h
      · have hya : y ≠ a := by rw [hxa] at hxy; exact Ne.symm hxy
        rw [hxa]
        exact (expand_six hU hI hab hya hyb h).1
    · by_cases hxb : x = b
      · by_cases hya : y = a
        · obtain ⟨w, hwx, hwy⟩ := h3 a b
          rw [hxb, hya]
          exact (expand_six hU hI hab hwx hwy h).2.2.2.2
        · have hyb : y ≠ b := by rw [hxb] at hxy; exact Ne.symm hxy
          rw [hxb]
          exact (expand_six hU hI hab hya hyb h).2.2.1
      · by_cases hya : y = a
        · rw [hya]
          exact (expand_six hU hI hab hxa hxb h).2.2.2.1
        · by_cases hyb : y = b
          · rw [hyb]
            exact (expand_six hU hI hab hxa hxb h).2.1
          · have hxb' : AlmostDecisiveFor F G x b := (expand_six hU hI hab hxa hxb h).2.1
            exact AlmostDecisiveFor_of_DecisiveFor
              (expand_right hU hI hxb (Ne.symm hxy) hyb hxb')
  obtain ⟨w, hwx, hwy⟩ := h3 x y
  exact decisiveFor_of_almostDecisiveFor hU hI hxy hwx hwy key

/-- **Arrow's theorem (existence of a dictator).**  A unanimous social welfare function
satisfying IIA, on at least three alternatives and finitely many voters, has a dictator. -/
