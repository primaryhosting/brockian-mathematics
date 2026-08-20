import RequestProject.Wedge

/-!
# Splitting the unit ball by three planes through the origin
-/

namespace Math

open MeasureTheory Metric Real Set
open scoped RealInnerProductSpace ENNReal

/-- The closed unit ball of `E3`, as a set. -/

lemma lintegral_radial :
    ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (2 * r * √(1 - r ^ 2)) = ENNReal.ofReal (2 / 3) := by
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext r
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h
      rcases le_total r 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · rcases eq_or_lt_of_le h' with h'' | h''
        · exact Or.inl ⟨h, h''.ge⟩
        · exact Or.inr h''
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  have hmeasf : Measurable fun r : ℝ => ENNReal.ofReal (2 * r * √(1 - r ^ 2)) := by fun_prop
  have hzero : ∫⁻ r in Ioi (1:ℝ), ENNReal.ofReal (2 * r * √(1 - r ^ 2)) = 0 := by
    rw [setLIntegral_eq_zero_iff' measurableSet_Ioi hmeasf.aemeasurable]
    filter_upwards with r hr
    have : √(1 - r ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith [mem_Ioi.mp hr])
    simp [this]
  rw [hsplit, lintegral_union measurableSet_Ioi (by simp [Set.disjoint_left]), hzero, add_zero]
  have hint : IntegrableOn (fun r : ℝ => 2 * r * √(1 - r ^ 2)) (Ioc 0 1) volume := by
    apply Continuous.integrableOn_Ioc
    fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal hint ?_]
  · congr 1
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact integral_radial
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have h0 : (0:ℝ) ≤ r := hr.1.le
    positivity

/-- The length of a vertical slice of the unit ball. -/
