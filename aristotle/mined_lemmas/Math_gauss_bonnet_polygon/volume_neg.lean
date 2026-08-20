import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_neg (S : Set E3) : volume ((fun x : E3 => -x) ⁻¹' S) = volume S := by
  rw [show (fun x : E3 => -x) ⁻¹' S = -S from rfl]
  exact Measure.measure_neg volume S

end Math

import Mathlib

/-!
# Basic definitions for the spherical Gauss–Bonnet (Girard) theorem

We work in `E3 = EuclideanSpace ℝ (Fin 3)`.

* `solidCone S` is the cone over a subset `S` of the unit sphere.
* `sphericalArea S = 3 * volume (solidCone S)`; this is the usual surface area
  (for `S` the whole sphere it gives `4 * π`, see `sphericalArea_sphere`).
* `sphericalTriangle A B C` is the geodesic triangle with vertices `A`, `B`, `C`.
* `sphericalAngle A B C` is the interior angle at the vertex `A`.
-/

namespace Math

open MeasureTheory Metric Real
open scoped RealInnerProductSpace

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The cone with apex the origin over a subset of the unit sphere. -/
