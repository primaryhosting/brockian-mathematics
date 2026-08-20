import Mathlib
namespace MS.Analysis

theorem extreme_value (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ c ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f c := by
  obtain ⟨c, hc, hmax⟩ :=
    (isCompact_Icc (a := a) (b := b)).exists_isMaxOn (Set.nonempty_Icc.2 hab) hf
  exact ⟨c, hc, fun x hx => hmax hx⟩
