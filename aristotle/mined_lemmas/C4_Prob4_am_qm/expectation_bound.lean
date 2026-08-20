import Mathlib
open Finset
namespace C4.Prob4

/-- AM–QM inequality. The nonnegativity hypothesis `hx` is part of the requested
statement, but it is not needed for the proof. -/

theorem expectation_bound {n : ℕ} (x : Fin n → ℝ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (M : ℝ) (hM : ∀ i, x i ≤ M) : ∑ i, p i * x i ≤ M := by
  calc ∑ i, p i * x i ≤ ∑ i, p i * M :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hp i)
    _ = M := by rw [← Finset.sum_mul, hs, one_mul]

end C4.Prob4

