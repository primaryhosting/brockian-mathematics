import Mathlib

/-!
# Exotic R 4
Category: Frontier — Fields Medal Work
Target: Frontier.exotic_R4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The model space and the category of smooth `4`-manifolds -/

/-- The model space `ℝ⁴`. -/
abbrev R4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The (boundaryless) model with corners of `ℝ⁴` on itself. -/
noncomputable abbrev I4 : ModelWithCorners ℝ R4 R4 := modelWithCornersSelf ℝ R4

/-- A `C^∞` smooth `4`-manifold without boundary: a topological space equipped with an atlas
of charts into `ℝ⁴` whose transition maps are `C^∞`. -/
structure Smooth4Manifold where
  /-- The underlying set of points of the manifold. -/
  Carrier : Type
  /-- The topology on the manifold. -/
  [topology : TopologicalSpace Carrier]
  /-- The atlas of charts with values in `ℝ⁴`. -/
  [charted : ChartedSpace R4 Carrier]
  /-- The transition maps of the atlas are `C^∞`. -/
  [manifold : IsManifold I4 ∞ Carrier]

attribute [instance] Smooth4Manifold.topology Smooth4Manifold.charted Smooth4Manifold.manifold

/-- `ℝ⁴` with its standard smooth structure, as a smooth `4`-manifold. -/

theorem Homeo.of_diffeo {M N : Smooth4Manifold} (h : Diffeo M N) : Homeo M N :=
  ⟨h.some.toHomeomorph⟩

/-! ## The statement of the theorem of Donaldson and Freedman -/

/-- `M` is an *exotic* `ℝ⁴`: a smooth `4`-manifold which is homeomorphic to `ℝ⁴` but not
diffeomorphic to it. -/
