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

theorem nonempty_homeomorph_sphere3_of_punctured (M : Type u) [TopologicalSpace M]
    (hM : IsClosedThreeManifold M) (p : M)
    (h : Nonempty ({x : M // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 3))) :
    Nonempty (M ≃ₜ Sphere3) := by
  obtain ⟨hcomp, ht2, -, -⟩ := hM
  obtain ⟨e⟩ := h
  exact ⟨homeomorphSphere3OfPunctured e⟩

/-- The hypothesis of the reduction is satisfiable: the 3-sphere is a closed 3-manifold which
has a point whose complement is homeomorphic to `ℝ³`. -/
