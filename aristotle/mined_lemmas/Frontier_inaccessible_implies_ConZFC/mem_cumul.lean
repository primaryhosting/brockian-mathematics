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

theorem mem_cumul {o : Ordinal.{u}} {x : ZFSet.{u}} : x ∈ cumul o ↔ x.rank < o := by
  induction o using Ordinal.induction generalizing x with
  | h o ih =>
    rw [cumul_def, ZFSet.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rw [ZFSet.mem_powerset] at hi
      have hle : x.rank ≤ typein (α := o.ToType) (· < ·) i := by
        rw [ZFSet.rank_le_iff]
        intro y hy
        exact (ih _ (typein_lt_self i)).1 (hi hy)
      exact lt_of_le_of_lt hle (typein_lt_self i)
    · intro h
      refine ⟨(enum (α := o.ToType) (· < ·)) ⟨x.rank, by rwa [type_toType]⟩, ?_⟩
      rw [ZFSet.mem_powerset]
      intro y hy
      have he : typein (α := o.ToType) (· < ·)
          ((enum (α := o.ToType) (· < ·)) ⟨x.rank, by rwa [type_toType]⟩) = x.rank :=
        typein_enum _ _
      rw [he, ih _ h]
      exact ZFSet.rank_lt_of_mem hy

