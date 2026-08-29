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

theorem Reach_eq_true_iff_reaches {K : ℕ} (hK : M.N ≤ 2 ^ K) (a b : Fin M.N) :
    Reach M K a b = true ↔ M.Reaches a b := by
  constructor
  · exact Reach_sound
  · intro h
    obtain ⟨n, hn⟩ := reaches_iff_exists_W.1 h
    have hb : b ∈ Rset M a M.N := Rset_subset_card n (mem_Rset.2 hn)
    exact Reach_of_W hK (mem_Rset.1 hb)

end CS

