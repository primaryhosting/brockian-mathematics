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

theorem card_cumul_lt (hκ : κ.IsInaccessible) :
    ∀ o : Ordinal.{u}, o < κ.ord → (cumul o).card < κ := by
  intro o
  induction o using Ordinal.induction with
  | h o ih =>
    intro ho
    rw [cumul_def]
    have h1 : Cardinal.lift.{u, u} (ZFSet.iUnion (fun i : o.ToType =>
        ZFSet.powerset (cumul ((typein (α := o.ToType) (· < ·)) i)))).card
        ≤ sum (fun i : o.ToType =>
            (ZFSet.powerset (cumul ((typein (α := o.ToType) (· < ·)) i))).card) :=
      ZFSet.lift_card_iUnion_le_sum_card
    rw [Cardinal.lift_id] at h1
    refine lt_of_le_of_lt h1 (sum_lt_of_isRegular hκ.isRegular ?_ ?_)
    · rw [mk_toType]
      exact Cardinal.lt_ord.1 ho
    · intro i
      rw [ZFSet.card_powerset]
      exact hκ.isStrongLimit.two_power_lt
        (ih _ (typein_lt_self i) ((typein_lt_self i).trans ho))

/-- A set of rank below `κ.ord` has fewer than `κ` elements. -/
