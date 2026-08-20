import Mathlib
namespace MS.Analysis

theorem intermediate_value (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (y : ℝ) (hy : y ∈ Set.Icc (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hf hy
  exact ⟨c, hc, hfc⟩
