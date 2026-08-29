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

def repRel₁ (n : ℕ) : (Fin n ⊕ Bool) → ((((Fin n ⊕ Unit) ⊕ Unit) ⊕ Unit) ⊕ Unit)
  | Sum.inl i => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))
  | Sum.inr false => Sum.inl (Sum.inl (Sum.inr ()))
  | Sum.inr true => Sum.inl (Sum.inr ())

/-- Relabelling of a replacement formula `φ(x, y, p⃗)` into the scope of `a, x, y, y'`,
sending `y` to the variable `y'`. -/
