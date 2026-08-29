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

@[simp] theorem realize_axRep (n : ℕ) (φ : setLang.Formula (Fin n ⊕ Bool)) :
    M ⊨ axRep n φ ↔ ∀ p : Fin n → M, ∀ a : M,
      (∀ x y y' : M, ((memM x a ∧ φ.Realize (Sum.elim p (fun b => cond b y x))) ∧
          φ.Realize (Sum.elim p (fun b => cond b y' x))) → y = y') →
      ∃ b : M, ∀ y : M, memM y b ↔ ∃ x : M, memM x a ∧
        φ.Realize (Sum.elim p (fun c => cond c y x)) := by
  simp only [axRep, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
    realize_allQ, realize_exQ, Formula.realize_iff, realize_memF, realize_up, Term.realize_var,
    Formula.realize_inf, Formula.realize_imp, Sum.elim_inr]
  refine forall_congr' fun p => ?_
  refine forall_congr' fun a => ?_
  refine imp_congr ?_ ?_
  · refine forall_congr' fun x => forall_congr' fun y => forall_congr' fun y' => ?_
    refine imp_congr ?_ Iff.rfl
    refine and_congr (and_congr Iff.rfl ?_) ?_
    · rw [iff_iff_eq]; congr 1
      funext i
      cases i with
      | inl i => rfl
      | inr b => cases b <;> rfl
    · rw [iff_iff_eq]; congr 1
      funext i
      cases i with
      | inl i => rfl
      | inr b => cases b <;> rfl
  · refine exists_congr fun b => forall_congr' fun y => ?_
    refine iff_congr Iff.rfl (exists_congr fun x => and_congr Iff.rfl ?_)
    rw [iff_iff_eq]; congr 1
    funext i
    cases i with
    | inl i => rfl
    | inr c => cases c <;> rfl

