/-
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

open Metric Set Topology Module

namespace Frontier

universe u

/-- The 3-sphere, realized as the unit sphere in 4-dimensional Euclidean space. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- `M` is a *closed 3-manifold*: a compact, Hausdorff, second countable space which is
locally homeomorphic to `ℝ³` (equivalently, a compact 3-manifold without boundary). -/

noncomputable def onePointComplHomeomorph {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (p : M) : OnePoint {x : M // x ≠ p} ≃ₜ M :=
  OnePoint.equivOfIsEmbeddingOfRangeEq p Subtype.val Topology.IsEmbedding.subtypeVal
    (by ext x; simp)

/-- If some point of a compact Hausdorff space `M` has complement homeomorphic to `ℝ³`, then
`M` is homeomorphic to the 3-sphere. -/
