import Mathlib
open Finset
namespace MS2.Probability
/-- Finite Markov inequality. The hypothesis `0 < a` is kept as stated, although the
proof does not need it (nonnegativity of `x` alone suffices). -/

theorem cauchy_schwarz_expect {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i, x i * y i)^2 ≤ (∑ i, (x i)^2) * (∑ i, (y i)^2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ x y

