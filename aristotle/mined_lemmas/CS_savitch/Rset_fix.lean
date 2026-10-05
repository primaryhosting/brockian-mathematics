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

theorem Rset_fix {a : Fin M.N} {i : ℕ} (h : Rset M a (i + 1) = Rset M a i) :
    ∀ j, i ≤ j → Rset M a j = Rset M a i := by
  have key : ∀ t, Rset M a (i + t) = Rset M a i := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        have e : i + (t + 1) = i + t + 1 := by omega
        rw [e, Rset_fix_step h t, ih]
  intro j hj
  obtain ⟨t, rfl⟩ : ∃ t, j = i + t := ⟨j - i, by omega⟩
  exact key t

