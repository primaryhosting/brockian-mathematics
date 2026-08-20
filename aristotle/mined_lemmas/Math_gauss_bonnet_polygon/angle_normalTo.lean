import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma angle_normalTo (h : Indep3 A B C) :
    angle (normalTo A C B) (normalTo A B C) = π - sphericalAngle A B C := by
  have hu : B - ⟪A, B⟫ • A ≠ 0 := tangent_ne_zero h
  have hv : C - ⟪A, C⟫ • A ≠ 0 := tangent_ne_zero h.perm₂
  have hD := inner_gram_pos hu (tangent_not_parallel h)
  have := angle_proj_proj hu hv hD
  rw [sphericalAngle]
  rw [← this]
  rfl

end

end Math

import Mathlib
import RequestProject.Angles
import RequestProject.Octants

/-!
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace Math

open MeasureTheory Metric Real Set InnerProductGeometry
open scoped RealInnerProductSpace ENNReal

/-- The cone over the whole unit sphere is the closed unit ball, so the sphere has area
`4 * π`: the normalisation of `sphericalArea` is the usual one. -/
