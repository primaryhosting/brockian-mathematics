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

theorem Rset_subset_card {a : Fin M.N} (n : ℕ) : Rset M a n ⊆ Rset M a M.N := by
  by_cases h : ∃ i < M.N, Rset M a (i + 1) = Rset M a i
  · obtain ⟨i, hi, hfix⟩ := h
    rcases Nat.lt_or_ge n M.N with hn | hn
    · exact Rset_mono (by omega)
    · have h1 : Rset M a n = Rset M a i := Rset_fix hfix n (by omega)
      have h2 : Rset M a M.N = Rset M a i := Rset_fix hfix M.N (by omega)
      rw [h1, h2]
  · push_neg at h
    have := Rset_card_grow (M := M) (a := a) M.N (fun j hj => h j hj)
    have hle : (Rset M a M.N).card ≤ M.N := by
      simpa using Finset.card_le_univ (Rset M a M.N)
    omega

/-- **Reachability is decided by the Savitch recursion**, provided `2 ^ K` is at least the
number of configurations. -/
