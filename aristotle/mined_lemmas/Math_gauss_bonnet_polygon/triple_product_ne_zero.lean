import RequestProject.Wedge

/-!
# Girard's relation for a solid cone over a spherical triangle

Given three vectors `u v w` in `ℝ³` in general position, the region
`Reg u v w`, the part of the unit ball where the three linear forms `⟪u,·⟫`, `⟪v,·⟫`, `⟪w,·⟫`
are nonnegative, has volume `((π - angle v w) + (π - angle u w) + (π - angle u v) - π)/3`.

This is Girard's theorem in disguise: the three quantities `π - angle · ·` are the dihedral
angles of the cone, and three times the volume of the cone is the area of the spherical
triangle it cuts out on the unit sphere.
-/

open MeasureTheory Metric Set Real InnerProductGeometry

namespace Math

/-- The closed half-space with inner normal `n`. -/

theorem triple_product_ne_zero {a b c : E3} (hb : ‖b‖ = 1)
    (hli : LinearIndependent ℝ ![a, b, c]) : (inner ℝ (cross b c) a : ℝ) ≠ 0 := by
  intro hD
  -- the cross product is orthogonal to a spanning family, hence zero
  obtain ⟨p, q, r, hx⟩ := span_of_linearIndependent hli (cross b c)
  have hzero : (inner ℝ (cross b c) (cross b c) : ℝ) = 0 := by
    nth_rewrite 2 [hx]
    rw [inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, hD, inner_cross_left, inner_cross_right]
    ring
  have hcross : cross b c = 0 := inner_self_eq_zero.1 hzero
  -- hence `b` and `c` are parallel
  have hnorm : ‖c - (inner ℝ b c : ℝ) • b‖ = 0 := by
    rw [← norm_cross_left b c hb, hcross, norm_zero]
  have : c = (inner ℝ b c : ℝ) • b := by
    have := norm_eq_zero.1 hnorm
    linear_combination (norm := module) this
  exact not_parallel_of_linearIndependent hli _ this

/-- **Gauss–Bonnet for a spherical triangle** (Girard's theorem): the area of a geodesic
triangle on the unit sphere, measured with the canonical (cone) measure on the sphere,
equals the sum of its three interior angles minus `π`. -/
