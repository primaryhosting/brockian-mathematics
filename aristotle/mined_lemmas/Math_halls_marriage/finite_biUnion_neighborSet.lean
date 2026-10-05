import Mathlib

/-!
# Halls Marriage
Category: Pure Mathematics
Target: Math.halls_marriage
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

namespace Math

open SimpleGraph

/-- The union of the neighborhoods of a finite vertex set is finite in a locally finite graph. -/

lemma finite_biUnion_neighborSet {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    {s : Set V} (hs : s.Finite) : (⋃ x ∈ s, G.neighborSet x).Finite :=
  hs.biUnion fun x _ => Set.toFinite (G.neighborSet x)

/-- If a graph has a perfect matching, then Hall's condition holds: every set of vertices
has a neighborhood at least as large. -/
