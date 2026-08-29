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

theorem Rset_card_grow {a : Fin M.N} (i : ℕ) (h : ∀ j < i, Rset M a (j + 1) ≠ Rset M a j) :
    i + 1 ≤ (Rset M a i).card := by
  induction i with
  | zero =>
      have : a ∈ Rset M a 0 := mem_Rset.2 (W_refl 0 a)
      exact Finset.card_pos.2 ⟨a, this⟩
  | succ i ih =>
      have hi : i + 1 ≤ (Rset M a i).card := ih (fun j hj => h j (by omega))
      have hne : Rset M a (i + 1) ≠ Rset M a i := h i (by omega)
      have hss : Rset M a i ⊂ Rset M a (i + 1) :=
        ⟨Rset_subset_succ a i, fun hcon => hne (Finset.Subset.antisymm hcon (Rset_subset_succ a i))⟩
      have := Finset.card_lt_card hss
      omega

