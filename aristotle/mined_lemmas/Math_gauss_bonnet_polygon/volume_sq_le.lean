import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma volume_sq_le (c : ℝ) : volume {t : ℝ | t ^ 2 ≤ c} = ENNReal.ofReal (2 * √c) := by
  rcases lt_or_ge c 0 with hc | hc
  · have hempty : {t : ℝ | t ^ 2 ≤ c} = ∅ := by
      ext t
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      nlinarith [sq_nonneg t]
    rw [hempty, Real.sqrt_eq_zero_of_nonpos hc.le]
    simp
  · have hset : {t : ℝ | t ^ 2 ≤ c} = Icc (-√c) (√c) := by
      ext t
      simp only [mem_setOf_eq, mem_Icc]
      constructor
      · intro h
        constructor <;> nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c, sq_nonneg (t - √c),
          sq_nonneg (t + √c)]
      · rintro ⟨h1, h2⟩
        nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c]
    rw [hset, Real.volume_Icc]
    congr 1
    ring

/-- Identification of `ℝ² × ℝ` with `Fin 3 → ℝ`. -/
