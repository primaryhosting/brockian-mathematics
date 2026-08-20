import Mathlib
open Finset
namespace MS.Inequalities

theorem cauchy_schwarz {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ a b
