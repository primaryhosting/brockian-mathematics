import Mathlib

/-!
# Heine Cantor
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.heine_cantor
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

namespace Topology

/-- **Heine–Cantor theorem**: a continuous map from a compact uniform space to a uniform
space is uniformly continuous. -/
theorem heine_cantor {X Y : Type*} [UniformSpace X] [UniformSpace Y] [CompactSpace X]
    {f : X → Y} (hf : Continuous f) : UniformContinuous f :=
  CompactSpace.uniformContinuous_of_continuous hf

/-- Metric-space corollary: a continuous function on a compact metric space is uniformly
continuous, in the `ε`–`δ` formulation. -/
theorem heine_cantor_metric {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    {f : X → Y} (hf : Continuous f) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → dist (f x) (f y) < ε :=
  fun ε hε => Metric.uniformContinuous_iff.mp (heine_cantor hf) ε hε

/-- The "on a compact set" version: a function continuous on a compact set `s` is uniformly
continuous on `s`. -/
theorem heine_cantor_on {X Y : Type*} [UniformSpace X] [UniformSpace Y] {s : Set X}
    (hs : IsCompact s) {f : X → Y} (hf : ∀ x ∈ s, ContinuousWithinAt f s x) :
    UniformContinuousOn f s :=
  hs.uniformContinuousOn_of_continuous hf

end Topology

