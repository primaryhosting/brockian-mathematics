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

theorem Rset_fix_succ {a : Fin M.N} {i : ℕ} (h : Rset M a (i + 1) = Rset M a i) :
    Rset M a (i + 2) = Rset M a (i + 1) := by
  apply Finset.Subset.antisymm _ (Rset_subset_succ a (i + 1))
  intro b hb
  rcases W_unsnoc (mem_Rset.1 hb) with hw | ⟨c, hc1, hc2⟩
  · exact mem_Rset.2 hw
  · have hc : c ∈ Rset M a i := h ▸ mem_Rset.2 hc1
    exact mem_Rset.2 (W_snoc (mem_Rset.1 hc) hc2)

