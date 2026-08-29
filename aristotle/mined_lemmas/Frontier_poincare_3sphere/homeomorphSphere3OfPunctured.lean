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

noncomputable def homeomorphSphere3OfPunctured {M : Type u} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {p : M} (e : {x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 3)) :
    M ≃ₜ Sphere3 :=
  (onePointComplHomeomorph p).symm.trans
    (e.onePointCongr.trans (onePointEquivSphereOfFinrankEq (ι := Fin 4) (by simp)))

/-! ### The punctured 3-sphere is `ℝ³` -/

instance : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

/-- Stereographic projection: the complement of a point in the 3-sphere is homeomorphic to
`ℝ³`. -/
