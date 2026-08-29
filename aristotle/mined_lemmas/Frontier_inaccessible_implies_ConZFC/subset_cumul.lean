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

theorem subset_cumul {x : ZFSet.{u}} : x ⊆ cumul x.rank := fun _ hy =>
  mem_cumul.2 (ZFSet.rank_lt_of_mem hy)

variable {κ : Cardinal.{u}}

/-- If `κ` is inaccessible then every level of the cumulative hierarchy below `κ` has
cardinality less than `κ`. -/
