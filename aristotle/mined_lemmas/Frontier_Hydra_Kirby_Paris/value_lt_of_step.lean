import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/

theorem value_lt_of_step {h h' : Hydra} (hs : Step h h') : value h' < value h := by
  induction hs with
  | root a b =>
    simp only [value_node, listValue_append, listValue_cons, listValue_nil, Ordinal.opow_zero,
      Ordinal.one_nadd]
    exact Ordinal.nadd_lt_nadd_left (Order.lt_succ _) _
  | copy a b c d n =>
    have hu : value (.node (c ++ d)) < value (.node (c ++ .node [] :: d)) := by
      simp only [value_node, listValue_append, listValue_cons, listValue_nil, Ordinal.opow_zero,
        Ordinal.one_nadd]
      exact Ordinal.nadd_lt_nadd_left (Order.lt_succ _) _
    have hpow : ω ^ value (Hydra.node (c ++ d))
        < ω ^ value (Hydra.node (c ++ Hydra.node [] :: d)) :=
      (Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 hu
    have hrep : listValue (List.replicate n (Hydra.node (c ++ d)))
        < ω ^ value (Hydra.node (c ++ Hydra.node [] :: d)) :=
      listValue_replicate_lt _ _ n hpow
    simp only [value_node, listValue_append, listValue_cons] at hrep ⊢
    exact Ordinal.nadd_lt_nadd_left (Ordinal.nadd_lt_nadd_right hrep _) _
  | deep a b u u' _ ih =>
    simp only [value_node, listValue_append, listValue_cons]
    exact Ordinal.nadd_lt_nadd_left
      (Ordinal.nadd_lt_nadd_right ((Ordinal.opow_lt_opow_iff_right one_lt_omega0).2 ih) _) _

/-- A living hydra always has a legal move: Hercules can cut off some head.  (This shows
that the termination statement below is not vacuous.) -/
