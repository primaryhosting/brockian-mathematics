import Mathlib
namespace MS.Analysis

theorem cantor_uncountable : ¬ (Set.univ : Set ℝ).Countable :=
  Cardinal.not_countable_real
end MS.Analysis

