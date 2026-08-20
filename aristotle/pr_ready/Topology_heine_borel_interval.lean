/-!
# Heine Borel Interval
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.heine_borel_interval
Statement: A closed bounded interval of the reals is compact: Set.Icc a b is compact (IsCompact (Set.Icc a b)) for real a b. (Use Mathlib's isCompact_Icc.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Topology

/-- **Heine–Borel for intervals**: a closed bounded interval `Set.Icc a b` of the reals
is compact. This is Mathlib's `isCompact_Icc`. -/
theorem heine_borel_interval (a b : ℝ) : IsCompact (Set.Icc a b) :=
  isCompact_Icc

end Topology

