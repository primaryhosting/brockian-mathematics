import Mathlib
open Finset
namespace Frontier.AnalysisCalculus


theorem qm_am {n : ℕ} (a : Fin n → ℝ) : (∑ i, a i) ^ 2 ≤ n * ∑ i, (a i)^2 := by
  simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)

end Frontier.AnalysisCalculus

