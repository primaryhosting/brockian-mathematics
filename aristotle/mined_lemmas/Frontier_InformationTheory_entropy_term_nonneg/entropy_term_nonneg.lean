import Mathlib
open Finset
namespace Frontier.InformationTheory

theorem entropy_term_nonneg (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ - p * Real.log p := by
  rcases eq_or_lt_of_le h0 with h | h
  · simp [← h]
  · have hlog : Real.log p ≤ 0 := Real.log_nonpos h0 h1
    nlinarith

