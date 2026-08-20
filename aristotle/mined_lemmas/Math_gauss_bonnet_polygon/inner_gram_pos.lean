import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma inner_gram_pos {u v : E3} (hu : u ≠ 0) (hnp : ∀ r : ℝ, v ≠ r • u) :
    0 < ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
  have hU : 0 < ⟪u, u⟫ := real_inner_self_pos.mpr hu
  set k : ℝ := ⟪u, v⟫ / ⟪u, u⟫ with hk
  have hw : v - k • u ≠ 0 := fun h => hnp k (by rw [← sub_eq_zero]; exact h)
  have hpos := real_inner_self_pos.mpr hw
  have key : ⟪v - k • u, v - k • u⟫ = ⟪v, v⟫ - ⟪u, v⟫ ^ 2 / ⟪u, u⟫ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm v u, hk]
    field_simp
    ring
  rw [key] at hpos
  have hmul : 0 < (⟪v, v⟫ - ⟪u, v⟫ ^ 2 / ⟪u, u⟫) * ⟪u, u⟫ := mul_pos hpos hU
  field_simp at hmul
  nlinarith [hmul]

/-- The two "projected" vectors make an angle supplementary to the angle between `u` and `v`. -/
