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

def IsClosedManifold (n : ℕ) (M : Type u) [TopologicalSpace M] : Prop :=
  CompactSpace M ∧ T2Space M ∧ Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) M)

/-- The standard `n`-sphere, as the unit sphere of `ℝⁿ⁺¹`. -/
abbrev Sphere (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The statement of the Poincaré conjecture in dimension 3 (Perelman's theorem):
every simply connected closed 3-manifold is homeomorphic to the 3-sphere. -/
