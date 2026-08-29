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

theorem addSink_reaches_aux (M : Machine) (y : Fin (M.addSink).N)
    (h : (M.addSink).Reaches (M.addSink).start y) :
    (∃ hy : y.val < M.N, M.Reaches M.start ⟨y.val, hy⟩) ∨ (y.val = M.N ∧ M.Accepts) := by
  induction h with
  | refl =>
      exact Or.inl ⟨M.start.isLt, by simpa using Relation.ReflTransGen.refl⟩
  | @tail x y h hs ih =>
      rcases ih with ⟨hx, hrx⟩ | ⟨hx, hacc⟩
      · rw [addSink_step_eq] at hs
        rw [dif_pos hx] at hs
        by_cases hy : y.val < M.N
        · rw [dif_pos hy] at hs
          exact Or.inl ⟨hy, hrx.tail hs⟩
        · rw [dif_neg hy] at hs
          have hylt : y.val < M.N + 1 := by simpa using y.isLt
          refine Or.inr ⟨by omega, ⟨⟨x.val, hx⟩, hrx, hs⟩⟩
      · rw [addSink_step_eq] at hs
        rw [dif_neg (by omega)] at hs
        exact absurd hs (by simp)

/-- `M` accepts iff the sink of `M.addSink` is reachable from its start configuration. -/
