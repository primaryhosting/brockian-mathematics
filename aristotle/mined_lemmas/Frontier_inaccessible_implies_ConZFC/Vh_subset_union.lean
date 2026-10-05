import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

We formalize the classical theorem that an inaccessible cardinal `κ` yields a model of `ZFC`,
namely the level `V_κ` of the cumulative hierarchy, and deduce that `ZFC` (as a first-order
theory in the language of set theory) is consistent, i.e. satisfiable.

The development proceeds in the following steps:

* `Frontier.Vh` : the cumulative hierarchy `V_o` of `ZFSet`s, with `x ∈ V_o ↔ rank x < o`.
* `Frontier.card_Vh_lt` : if `κ` is inaccessible and `o < κ.ord` then `V_o` has cardinality `< κ`.
* `Frontier.setLang` : the first-order language of set theory (one binary relation).
* `Frontier.ZFC` : the theory `ZFC`, with the separation and replacement schemes.
* `Frontier.VSet κ` : the model, the set of `ZFSet`s of rank `< κ.ord`.
* `Frontier.inaccessible_implies_ConZFC` : an inaccessible cardinal gives `Con(ZFC)`.
-/

universe u

namespace Frontier

open Ordinal Cardinal ZFSet

/-! ### The cumulative hierarchy -/

/-- The `o`-th level of the cumulative hierarchy of `ZFSet`s. -/

theorem Vh_subset_union (o : Ordinal.{u}) :
    Vh o ⊆ ⋃ (i : Shrink.{u} (Set.Iio o)),
      ZFSet.powerset (Vh ((equivShrink (Set.Iio o)).symm i : Set.Iio o).1) := by
  intro x hx
  rw [mem_Vh] at hx
  rw [ZFSet.mem_iUnion]
  refine ⟨equivShrink (Set.Iio o) ⟨x.rank, hx⟩, ?_⟩
  rw [Equiv.symm_apply_apply, ZFSet.mem_powerset]
  intro y hy
  exact mem_Vh.2 (ZFSet.rank_lt_of_mem hy)

/-- Below an inaccessible cardinal, every level of the cumulative hierarchy is small. -/
