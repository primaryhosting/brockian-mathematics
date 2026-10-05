import Mathlib

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

import RequestProject.Savitch.Machine

/-!
# Reduction to single-target reachability

`CS.addSink M` adds one new configuration (the *sink*) to `M`, with an edge from every
accepting configuration of `M` to the sink and no outgoing edge from the sink.  Then `M`
accepts iff the sink is reachable from the start configuration of `addSink M`, so that
deciding acceptance becomes deciding reachability between two *fixed* configurations.
-/

namespace CS

namespace Machine

/-- Add a sink configuration reachable exactly from the accepting configurations. -/

theorem ofFn_reaches_iff {S : Type} [Fintype S] [DecidableEq S] (f : S → S) (init : S)
    (acc : S → Bool) (c : Fin (ofFn f init acc).N) :
    (ofFn f init acc).Reaches (ofFn f init acc).start c ↔
      ∃ t, (Fintype.equivFin S) (f^[t] init) = c := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail h hs ih =>
        obtain ⟨t, ht⟩ := ih
        refine ⟨t + 1, ?_⟩
        simp only [ofFn, decide_eq_true_eq] at hs
        rw [Function.iterate_succ_apply']
        rw [← hs, ← ht, Equiv.symm_apply_apply]
  · rintro ⟨t, rfl⟩
    induction t with
    | zero => exact Relation.ReflTransGen.refl
    | succ t ih =>
        refine Relation.ReflTransGen.tail ih ?_
        simp only [ofFn, decide_eq_true_eq, Equiv.symm_apply_apply]
        rw [Function.iterate_succ_apply']

