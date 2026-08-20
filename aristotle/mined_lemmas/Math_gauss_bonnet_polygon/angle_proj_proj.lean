import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma angle_proj_proj {u v : E3} (hu : u ≠ 0) (hv : v ≠ 0)
    (hD : 0 < ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2) :
    angle (u - (⟪u, v⟫ / ⟪v, v⟫) • v) (v - (⟪v, u⟫ / ⟪u, u⟫) • u) = π - angle u v := by
  have hU : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  have hV : 0 < ⟪v, v⟫ := real_inner_self_pos.mpr hv
  have hvu : ⟪v, u⟫ = ⟪u, v⟫ := (real_inner_comm v u).symm
  rw [hvu]
  set U := ⟪u, u⟫ with hUdef
  set V := ⟪v, v⟫ with hVdef
  set p := ⟪u, v⟫ with hpdef
  set D := U * V - p ^ 2 with hDdef
  set X := u - (p / V) • v with hX
  set Y := v - (p / U) • u with hY
  have hXY : ⟪X, Y⟫ = -(p * D) / (U * V) := by
    simp only [hX, hY, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hvu, ← hUdef, ← hVdef, ← hpdef, hDdef]
    field_simp
    ring
  have hXX : ⟪X, X⟫ = D / V := by
    simp only [hX, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hvu, ← hUdef, ← hVdef, ← hpdef, hDdef]
    field_simp
    ring
  have hYY : ⟪Y, Y⟫ = D / U := by
    simp only [hY, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hvu, ← hUdef, ← hVdef, ← hpdef, hDdef]
    field_simp
    ring
  have hg : (0:ℝ) < √(U * V) := Real.sqrt_pos.mpr (by positivity)
  have hg2 : √(U * V) ^ 2 = U * V := Real.sq_sqrt (by positivity)
  have hnX : ‖X‖ = √(D / V) := by rw [← hXX]; exact norm_eq_sqrt_real_inner X
  have hnY : ‖Y‖ = √(D / U) := by rw [← hYY]; exact norm_eq_sqrt_real_inner Y
  have hnu : ‖u‖ = √U := norm_eq_sqrt_real_inner u
  have hnv : ‖v‖ = √V := norm_eq_sqrt_real_inner v
  have hprod : ‖X‖ * ‖Y‖ = D / √(U * V) := by
    rw [hnX, hnY, ← Real.sqrt_mul (by positivity)]
    have h1 : D / V * (D / U) = (D / √(U * V)) ^ 2 := by
      rw [div_pow, hg2]; field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
  have hprod2 : ‖u‖ * ‖v‖ = √(U * V) := by rw [hnu, hnv, ← Real.sqrt_mul (by positivity)]
  rw [angle, angle, hXY, hprod, hprod2]
  have hfin : ∀ g : ℝ, 0 < g → g ^ 2 = U * V → -(p * D) / (U * V) / (D / g) = -(p / g) := by
    intro g _ hgsq
    rw [← hgsq]
    field_simp
  rw [hfin _ hg hg2]
  exact Real.arccos_neg _

/-! ### The side normals of a spherical triangle -/

section

variable {A B C : E3}

/-- The tangent direction at `A` towards `B` is nonzero. -/
