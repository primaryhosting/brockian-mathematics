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

## Arrow's impossibility theorem

A *ranking* of a type `A` of alternatives is a strict total order (transitive, total on
distinct elements, asymmetric).  A *social welfare function* is a map
`F : (V → Ranking A) → Ranking A` sending each profile of individual rankings (one for each
voter `i : V`) to a social ranking.

We prove: if `V` is a finite nonempty set of voters, `A` has at least three elements, and `F`
satisfies unanimity (Pareto) and independence of irrelevant alternatives (IIA), then `F` has a
dictator.  Equivalently, no `F` satisfies unanimity, IIA and non-dictatorship
(`Frontier.arrow_impossibility`).

Mathlib does not contain Arrow's theorem, so the development is from scratch.  The proof is the
classical one: a *field expansion* lemma (semi-decisiveness over one pair implies decisiveness
over all pairs) followed by a *group contraction* lemma (a decisive coalition splits into two
parts, one of which is decisive), and then induction on the size of the coalition starting from
the grand coalition, which is decisive by unanimity.
-/

namespace Frontier

/-- A strict total order ("ranking") on the type of alternatives `A`. -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_total : ∀ {x y}, x ≠ y → rel x y ∨ rel y x
  rel_asymm : ∀ {x y}, rel x y → ¬ rel y x

namespace Ranking

variable {A : Type*}


theorem exists_dictator [Fintype V] [Nonempty V]
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (F : (V → Ranking A) → Ranking A) (hPar : Pareto F) (hIIA : IIA F) :
    ∃ i : V, IsDictator F i := by
  classical
  have hdec : DecisiveAll F (Finset.univ : Finset V) := by
    intro x y _ P hP
    exact hPar P x y fun i => hP i (Finset.mem_univ i)
  obtain ⟨i, -, hi⟩ := exists_decisive_singleton hPar hIIA h3 (Finset.univ : Finset V).card
    Finset.univ le_rfl Finset.univ_nonempty hdec
  refine ⟨i, fun P x y hxy => ?_⟩
  by_cases hne : x = y
  · subst hne; exact absurd hxy ((P i).rel_irrefl x)
  · refine hi x y hne P ?_
    intro j hj
    rw [Finset.mem_singleton.1 hj]
    exact hxy

/-- **Arrow's impossibility theorem**: for at least three alternatives, no social welfare
function satisfies unanimity, independence of irrelevant alternatives, and
non-dictatorship. -/
