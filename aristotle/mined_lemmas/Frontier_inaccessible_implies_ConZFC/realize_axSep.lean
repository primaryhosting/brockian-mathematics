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

@[simp] theorem realize_axSep (n : ℕ) (φ : setLang.Formula (Fin n ⊕ Unit)) :
    M ⊨ axSep n φ ↔ ∀ p : Fin n → M, ∀ a : M, ∃ b : M, ∀ x : M,
      memM x b ↔ (memM x a ∧ φ.Realize (Sum.elim p (fun _ => x))) := by
  simp only [axSep, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
    realize_allQ, realize_exQ, Formula.realize_iff, realize_memF, realize_up, Term.realize_var,
    Formula.realize_inf, Sum.elim_inr]
  refine forall_congr' fun p => forall_congr' fun a => exists_congr fun b => forall_congr' fun x =>
    iff_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [iff_iff_eq]
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr u => cases u; rfl

