import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Metric Module Set Topology

/-- The standard `3`-sphere, realized as the unit sphere of `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The statement of the **Poincaré conjecture** (a theorem of Perelman): every simply
connected closed (= compact, without boundary) topological `3`-manifold is homeomorphic to
the `3`-sphere.

Being a closed `3`-manifold is encoded as: Hausdorff, compact, and locally modelled on
`ℝ³` (a `ChartedSpace (EuclideanSpace ℝ (Fin 3))` structure). Note that compactness together
with the charted space structure automatically gives second countability. -/

noncomputable def onePointComplSingletonHomeo {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (p : X) : OnePoint ({p}ᶜ : Set X) ≃ₜ X :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p Subtype.val IsEmbedding.subtypeVal (by
    ext x; simp)

/-- The one-point compactification of `ℝ³` is the `3`-sphere. -/
