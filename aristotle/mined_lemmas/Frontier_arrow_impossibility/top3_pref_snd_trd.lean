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

lemma top3_pref_snd_trd {x y z : α} (r : Ranking α) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (top3 x y z r).pref y z := by
  rw [top3, moveTop_pref x _ (Ne.symm hxy) (Ne.symm hxz)]
  exact moveTop_pref_top y _ (Ne.symm hyz)

/-- Every type carries at least one ranking. -/
instance instNonempty (α : Type*) : Nonempty (Ranking α) := by
  haveI := (@WellOrderingRel.isWellOrder α)
  haveI : DecidableRel (@WellOrderingRel α) := fun _ _ => Classical.propDecidable _
  letI : LinearOrder α := linearOrderOfSTO (@WellOrderingRel α)
  exact ⟨{ rel := fun x y => y ≤ x
           rel_total := fun x y => le_total y x
           rel_trans := fun h h' => le_trans h' h
           rel_antisymm := fun h h' => le_antisymm h' h }⟩

end Ranking

open Ranking

section Arrow

variable {V α : Type*} (F : (V → Ranking α) → Ranking α)

/-- Pareto/unanimity: if every voter strictly prefers `x` to `y`, so does society. -/
