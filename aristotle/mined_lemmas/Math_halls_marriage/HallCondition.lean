/-
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The *Hall condition* for a graph `G`: every set of vertices `s` has at least as many
neighbours (counted in the union of the neighbourhoods of its elements) as it has elements. -/

def HallCondition (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard

/-- The neighbourhood of a finite set of vertices in a locally finite graph is finite. -/
