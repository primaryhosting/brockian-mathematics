import Brockian.FordCircles
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# Ford-circle centers in the hyperbolic upper half-plane

Ford circles are Euclidean circles tangent to the boundary of the Poincaré upper half-plane;
geometrically they are horocycles.  This adapter places every positive-denominator Ford center in
Mathlib's upper-half-plane manifold and records the integral-translation symmetry as a hyperbolic
isometry.

The full modular quotient is intentionally absent: the modular action has elliptic fixed points,
so its quotient is naturally an orbifold unless one passes to suitable torsion-free data.
-/

namespace Brockian.FordHorocycles

open Complex UpperHalfPlane
open Brockian.FordCircles

noncomputable section

/-- The center of a positive-denominator Ford circle as a point of the upper half-plane. -/
def fordCenterH (a : ℤ) (q : ℕ) (hq : 0 < q) : ℍ :=
  ⟨fordCenter a q, by simpa using fordRadius_pos hq⟩

@[simp] theorem coe_fordCenterH (a : ℤ) (q : ℕ) (hq : 0 < q) :
    (fordCenterH a q hq : ℂ) = fordCenter a q := rfl

@[simp] theorem fordCenterH_re (a : ℤ) (q : ℕ) (hq : 0 < q) :
    (fordCenterH a q hq).re = (a : ℝ) / (q : ℝ) :=
  fordCenter_re a q

@[simp] theorem fordCenterH_im (a : ℤ) (q : ℕ) (hq : 0 < q) :
    (fordCenterH a q hq).im = fordRadius q :=
  fordCenter_im a q

/-- Adding one to the rational base point is the real-translation action on the upper half-plane. -/
theorem fordCenterH_int_translate (a n : ℤ) (q : ℕ) (hq : 0 < q) :
    fordCenterH (a + n * q) q hq = (n : ℝ) +ᵥ fordCenterH a q hq := by
  apply UpperHalfPlane.coe_injective
  simp only [coe_fordCenterH, coe_vadd, fordCenter]
  push_cast
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp
  ring

/-- Integral translation of Ford centers preserves the hyperbolic distance. -/
theorem dist_fordCenterH_int_translate (a c n : ℤ) (q d : ℕ)
    (hq : 0 < q) (hd : 0 < d) :
    dist (fordCenterH (a + n * q) q hq) (fordCenterH (c + n * d) d hd) =
      dist (fordCenterH a q hq) (fordCenterH c d hd) := by
  rw [fordCenterH_int_translate, fordCenterH_int_translate]
  exact (UpperHalfPlane.isometry_real_vadd (n : ℝ)).dist_eq _ _

end

end Brockian.FordHorocycles
