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

noncomputable def spherePuncturedHomeomorph (v : Sphere3) :
    {x : Sphere3 // x ≠ v} ≃ₜ EuclideanSpace ℝ (Fin 3) :=
  let e := stereographic' 3 v
  (Homeomorph.setCongr (s := {x : Sphere3 | x ≠ v}) (t := e.source)
      (by rw [stereographic'_source]; rfl)).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target v)).trans (Homeomorph.Set.univ _)))

/-! ### The 3-sphere is a closed 3-manifold -/

