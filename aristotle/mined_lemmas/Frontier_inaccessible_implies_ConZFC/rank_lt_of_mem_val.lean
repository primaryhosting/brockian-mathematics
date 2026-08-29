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

theorem rank_lt_of_mem_val {x : VSet κ} {z : ZFSet.{u}} (hz : z ∈ x.1) : z.rank < κ.ord :=
  (ZFSet.rank_lt_of_mem hz).trans x.2

/-- The element of `V_κ` determined by a member of an element of `V_κ`. -/
