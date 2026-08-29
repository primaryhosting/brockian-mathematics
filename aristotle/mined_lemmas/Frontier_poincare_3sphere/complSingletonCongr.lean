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

def complSingletonCongr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : (({x}ᶜ : Set X)) ≃ₜ (({e x}ᶜ : Set Y)) :=
  Homeomorph.subtype e (fun a => by simp [e.injective.eq_iff])

/-! ## The base case: the 3-sphere itself -/

/-- **Base case.** The 3-sphere is a compact Hausdorff charted space over `ℝ³`, i.e. a closed
topological 3-manifold, and (as required by the punctured criterion) deleting a point from it
yields a space homeomorphic to `ℝ³`. -/
