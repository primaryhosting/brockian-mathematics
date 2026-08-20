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


lemma decisiveAll_of_semiDecisive (hPar : Pareto F) (hIIA : IIA F)
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) {S : Finset V} {p q : A}
    (hpq : p ≠ q) (hsd : SemiDecisive F S p q) : DecisiveAll F S := by
  have stepA : ∀ {u v : A}, u ≠ v → SemiDecisive F S u v →
      ∀ w : A, w ≠ u → w ≠ v → Decisive F S u w :=
    fun huv hs w hwu hwv => decisive_fst hPar hIIA huv hwu hwv hs
  have stepB : ∀ {u v : A}, u ≠ v → SemiDecisive F S u v →
      ∀ w : A, w ≠ u → w ≠ v → Decisive F S w v :=
    fun huv hs w hwu hwv => decisive_snd hPar hIIA huv hwu hwv hs
  -- `S` is decisive for every pair `(p, t)`
  have step1 : ∀ t : A, t ≠ p → Decisive F S p t := by
    intro t ht
    by_cases htq : t = q
    · subst htq
      obtain ⟨z, hzp, hzt⟩ := exists_third h3 p t
      have d1 : Decisive F S p z := stepA hpq hsd z hzp hzt
      have s1 : SemiDecisive F S p z := semiDecisive_of_decisive (Ne.symm hzp) d1
      exact stepA (Ne.symm hzp) s1 t ht (Ne.symm hzt)
    · exact stepA hpq hsd t ht htq
  -- hence for every pair `(u, t)` with `t ≠ p`
  have step2 : ∀ t : A, t ≠ p → ∀ u : A, u ≠ t → Decisive F S u t := by
    intro t ht u hu
    by_cases hup : u = p
    · subst hup; exact step1 t ht
    · exact stepB (Ne.symm ht) (semiDecisive_of_decisive (Ne.symm ht) (step1 t ht)) u hup hu
  -- and finally for the pairs `(u, p)`
  have step3 : ∀ u : A, u ≠ p → Decisive F S u p := by
    intro u hu
    obtain ⟨z, hzp, hzu⟩ := exists_third h3 p u
    have d : Decisive F S u z := step2 z hzp u (Ne.symm hzu)
    exact stepA (Ne.symm hzu) (semiDecisive_of_decisive (Ne.symm hzu) d) p (Ne.symm hu)
      (Ne.symm hzp)
  intro x y hxy
  by_cases hy : y = p
  · subst hy; exact step3 x hxy
  · exact step2 y hy x hxy

/-- Group contraction: if a decisive coalition splits into two disjoint parts, one of the
parts is decisive. -/
