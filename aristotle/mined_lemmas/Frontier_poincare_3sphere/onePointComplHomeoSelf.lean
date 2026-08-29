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
open scoped OnePoint

open Metric Topology

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- `ℝ³`, the model space for `3`-dimensional topological manifolds. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `𝕊³`, the unit sphere in `ℝ⁴`. -/
local notation "𝕊³" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-! ## The statement of the Poincaré conjecture -/

/-- **The 3-dimensional topological Poincaré conjecture** (Perelman, 2003).

Every simply connected, closed (compact, boundaryless) topological 3-manifold is homeomorphic
to the 3-sphere.  A *closed topological 3-manifold* is a compact Hausdorff space equipped with
a charted space structure modelled on `ℝ³`.

This is the statement only; it is not proved here (and is not available in Mathlib either:
Mathlib records it as `SimplyConnectedSpace.nonempty_homeomorph_sphere_three`, a `proof_wanted`).
The theorem `Frontier.poincare_3sphere` below proves a *reduction* of this statement to a
purely local one. -/

noncomputable def onePointComplHomeoSelf (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] (x : X) : OnePoint ({x}ᶜ : Set X) ≃ₜ X :=
  OnePoint.equivOfIsEmbeddingOfRangeEq x Subtype.val Topology.IsEmbedding.subtypeVal
    Subtype.range_coe

/-- If `e : X ≃ₜ Y` is a homeomorphism, then deleting `x` from `X` and `e x` from `Y` gives
homeomorphic spaces. -/
