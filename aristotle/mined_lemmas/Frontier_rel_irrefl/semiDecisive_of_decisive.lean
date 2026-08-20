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


lemma semiDecisive_of_decisive {S : Finset V} {x y : A} (hxy : x ≠ y)
    (h : Decisive F S x y) : SemiDecisive F S x y := by
  classical
  refine ⟨fun i => if i ∈ S then mkRank (fun z => if z = x then 0 else if z = y then 1 else 2)
      else mkRank (fun z => if z = y then 0 else if z = x then 1 else 2), ?_, ?_, ?_⟩
  · intro i hi
    simp only [if_pos hi]
    exact mkRank_of_lt (by simp [Ne.symm hxy])
  · intro i hi
    simp only [if_neg hi]
    exact mkRank_of_lt (by simp [hxy])
  · refine h _ ?_
    intro i hi
    simp only [if_pos hi]
    exact mkRank_of_lt (by simp [Ne.symm hxy])

/-- Field expansion, step A: if `S` is semi-decisive for `(p, q)` then it is decisive for
`(p, r)` for every third alternative `r`. -/
