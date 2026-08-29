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

def IsClosedThreeManifold (M : Type u) [TopologicalSpace M] : Prop :=
  CompactSpace M ∧ T2Space M ∧ SecondCountableTopology M ∧
    ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3))

/-- **The Poincaré conjecture** (Perelman): every simply-connected closed 3-manifold is
homeomorphic to the 3-sphere. -/
