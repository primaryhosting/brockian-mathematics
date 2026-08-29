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

theorem sphere3_isClosedThreeManifold : IsClosedThreeManifold Sphere3 := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun x => ?_⟩
  refine ⟨{y : Sphere3 | y ≠ -x}, isOpen_compl_singleton, ?_, ⟨?_⟩⟩
  · have hx : (x : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
      intro h
      have := x.2
      simp [h] at this
    simp only [Set.mem_setOf_eq, ne_eq]
    intro h
    apply hx
    have : (x : EuclideanSpace ℝ (Fin 4)) = -(x : EuclideanSpace ℝ (Fin 4)) := congrArg Subtype.val h
    linear_combination (norm := module) (2⁻¹ : ℝ) • this
  · exact spherePuncturedHomeomorph (-x)

/-- Pointwise form of the reduction: a closed 3-manifold with a point whose complement is
homeomorphic to `ℝ³` is homeomorphic to the 3-sphere. (Simple connectedness is not needed:
it is only used to produce such a point.) -/
