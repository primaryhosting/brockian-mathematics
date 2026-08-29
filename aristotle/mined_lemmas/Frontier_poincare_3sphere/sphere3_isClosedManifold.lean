/-
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

universe u

/-! ## Formalizing the statement

We formalize "closed `n`-manifold" as: a compact Hausdorff space which is locally
homeomorphic to `ℝⁿ` (i.e. carries a `ChartedSpace (EuclideanSpace ℝ (Fin n))`
structure).  "Closed" here means compact and without boundary, as usual.
-/

/-- `IsClosedManifold n M` says that the topological space `M` is a closed
(= compact, boundaryless) topological `n`-manifold: it is compact, Hausdorff and
locally homeomorphic to `EuclideanSpace ℝ (Fin n)`. -/

theorem sphere3_isClosedManifold : IsClosedManifold 3 (Sphere 3) :=
  ⟨inferInstance, inferInstance, ⟨inferInstance⟩⟩

/-! ## A Lean-checked reduction

A continuous bijection from a compact space to a Hausdorff space is automatically a
homeomorphism.  Since a closed manifold is compact and the 3-sphere is Hausdorff, in
order to prove the Poincaré conjecture it suffices to produce a continuous bijection
`M → S³`; continuity of the inverse comes for free. -/

/-- Turning a continuous bijection out of a compact space into a homeomorphism. -/
