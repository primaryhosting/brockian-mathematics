/-
# Heine Cantor
Category: Frontier Wave 2 (deeper machinery)
Target: Topology.heine_cantor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- **Heine–Cantor theorem**: a continuous map from a compact uniform space to any uniform
space is uniformly continuous.

The proof is the standard compactness argument, phrased with filters: on a compact space the
uniformity is the supremum of the neighbourhood filters of the points of the diagonal
(`compactSpace_uniformity`), and continuity of `f × f` sends `𝓝 (x, x)` to `𝓝 (f x, f x)`,
which is below the uniformity of the target (`nhds_le_uniformity`). -/
theorem heine_cantor {X Y : Type*} [UniformSpace X] [UniformSpace Y] [CompactSpace X]
    {f : X → Y} (hf : Continuous f) : UniformContinuous f := by
  have hmap : Continuous (fun p : X × X => (f p.1, f p.2)) :=
    (hf.comp continuous_fst).prodMk (hf.comp continuous_snd)
  rw [UniformContinuous, compactSpace_uniformity, Filter.tendsto_iSup]
  intro x
  have h1 : Filter.Tendsto (fun p : X × X => (f p.1, f p.2)) (nhds (x, x)) (nhds (f x, f x)) :=
    hmap.tendsto (x, x)
  exact h1.mono_right (nhds_le_uniformity (f x))

/-- Metric-space form of Heine–Cantor: a continuous function on a compact metric space is
uniformly continuous in the `ε`-`δ` sense. -/
theorem heine_cantor_metric {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    {f : X → Y} (hf : Continuous f) :
    ∀ ε > 0, ∃ δ > 0, ∀ x y : X, dist x y < δ → dist (f x) (f y) < ε :=
  fun ε hε => Metric.uniformContinuous_iff.mp (heine_cantor hf) ε hε

end Topology

