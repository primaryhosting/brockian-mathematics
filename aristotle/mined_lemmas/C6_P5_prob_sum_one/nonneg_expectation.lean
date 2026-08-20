import Mathlib
open Finset
namespace C6.P5

theorem nonneg_expectation {n : ℕ} (x p : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ ∑ i, p i * x i :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hx i)
end C6.P5

