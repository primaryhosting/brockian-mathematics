/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Metric Set Module Real
open scoped RealInnerProductSpace ENNReal Pointwise

namespace Math

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The cross product of two vectors of `ℝ³`. -/

theorem volume_split_hemi (S : Set E3) (hS : MeasurableSet S) (hsub : S ⊆ {x : E3 | ‖x‖ < 1})
    {w : E3} (hw : w ≠ 0) :
    volume S = volume (S ∩ hemiCone w) + volume (S ∩ hemiCone (-w)) := by
  have e1 : S ∩ {x : E3 | 0 < ⟪w, x⟫} = S ∩ hemiCone w := by
    ext x; exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hsub h1, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  have e2 : S ∩ {x : E3 | 0 < ⟪-w, x⟫} = S ∩ hemiCone (-w) := by
    ext x; exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hsub h1, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  rw [← e1, ← e2]
  exact volume_split S hS hw

/-- Girard's theorem, in terms of the outer normals of the three sides. -/
