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

theorem reaches_iff_exists_W {a b : Fin M.N} : M.Reaches a b ↔ ∃ n, W M n a b = true := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, W_refl 0 a⟩
    | tail h hs ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, W_snoc hn hs⟩
  · rintro ⟨n, hn⟩
    induction n generalizing a with
    | zero =>
        rw [W_zero] at hn
        exact (of_decide_eq_true hn) ▸ Relation.ReflTransGen.refl
    | succ n ih =>
        rcases (W_succ_iff n a b).1 hn with rfl | ⟨c, hc, hw⟩
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.head hc (ih hw)

/-- A walk of length at most `2 ^ k` is found by the Savitch recursion at level `k`. -/
