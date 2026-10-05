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

@[simp] theorem realize_exQ {φ : setLang.Formula (α ⊕ Unit)} {v : α → M} :
    (exQ φ).Realize v ↔ ∃ x : M, φ.Realize (Sum.elim v (fun _ => x)) := by
  simp only [exQ, Formula.realize_iExs]
  exact ⟨fun ⟨i, h⟩ => ⟨i (), by rwa [elim_unit_ext]⟩,
    fun ⟨x, h⟩ => ⟨fun _ => x, by simpa using h⟩⟩

end Semantics

/-! ### The finitely many non-scheme axioms -/

/-- Extensionality: `∀ x y, (∀ z, z ∈ x ↔ z ∈ y) → x = y`. -/
