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


lemma exists_decisive_singleton [DecidableEq V] (hPar : Pareto F) (hIIA : IIA F)
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) :
    ∀ (n : ℕ) (S : Finset V), S.card ≤ n → S.Nonempty → DecisiveAll F S →
      ∃ i ∈ S, DecisiveAll F {i} := by
  intro n
  induction n with
  | zero =>
    intro S hcard hne _
    exact absurd (Finset.card_pos.2 hne) (by omega)
  | succ n ih =>
    intro S hcard hne hdec
    obtain ⟨i, hi⟩ := hne
    by_cases hsing : S = {i}
    · exact ⟨i, hi, hsing ▸ hdec⟩
    · have hsplit : ({i} ∪ S.erase i : Finset V) = S := by
        rw [Finset.singleton_union, Finset.insert_erase hi]
      have hdisj : Disjoint ({i} : Finset V) (S.erase i) :=
        Finset.disjoint_singleton_left.2 (Finset.notMem_erase i S)
      have hne' : (S.erase i).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hc
        rcases (Finset.erase_eq_empty_iff _ _).1 hc with hc' | hc'
        · exact absurd hi (by simp [hc'])
        · exact hsing hc'
      have hcard' : (S.erase i).card ≤ n := by
        have := Finset.card_erase_of_mem hi
        have h2 := Finset.card_pos.2 ⟨i, hi⟩
        omega
      have hdec' : DecisiveAll F ({i} ∪ S.erase i) := by rw [hsplit]; exact hdec
      rcases decisiveAll_split hPar hIIA h3 hdisj hdec' with hL | hR
      · exact ⟨i, hi, hL⟩
      · obtain ⟨j, hj, hjd⟩ := ih (S.erase i) hcard' hne' hR
        exact ⟨j, Finset.mem_of_mem_erase hj, hjd⟩

/-- **Arrow's theorem** (dictator form): a social welfare function on at least three
alternatives satisfying unanimity and IIA has a dictator. -/
