import Mathlib

/-!
# The cumulative hierarchy and inaccessible cardinals

This file defines the von Neumann cumulative hierarchy `Frontier.cumul o` inside `ZFSet`,
characterizes its members by rank, and proves the two facts about an inaccessible cardinal `κ`
that are needed to see that `V_κ` is a model of ZFC:

* `Frontier.card_lt_of_rank_lt`: a set of rank `< κ.ord` has cardinality `< κ`;
* `Frontier.rank_range_lt`: `V_κ` is closed under images of small families (replacement).
-/

open Ordinal Cardinal

namespace Frontier

/-- The von Neumann cumulative hierarchy `V_o`, as a `ZFSet`. -/

theorem no_universal_set_of_models_ZFC {M : Type*} [setLang.Structure M] (h : M ⊨ ZFC) :
    ¬ ∃ u : M, ∀ x : M, memM x u := by
  rintro ⟨u, hu⟩
  have hsep := (models_ZFC_iff.1 h).2.1 0
    (Formula.not (memF (Term.var (Sum.inr ())) (Term.var (Sum.inr ()))))
  rw [realize_axSep] at hsep
  obtain ⟨b, hb⟩ := hsep (fun i => i.elim0) u
  have hb' : ∀ x : M, memM x b ↔ ¬ memM x x := by
    intro x
    rw [hb x]
    simp [hu x]
  exact (fun hbb => (hb' b).1 hbb hbb) ((hb' b).2 (fun hbb => (hb' b).1 hbb hbb))

/-- Consistency of any extension of ZFC — in particular of `ZFC` together with an axiom
asserting the existence of an inaccessible cardinal — implies the consistency of ZFC. -/
