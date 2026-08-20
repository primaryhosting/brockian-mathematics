import Mathlib
open Finset
namespace MS2.Prob2

/-- AM–GM for three nonnegative reals. -/

theorem triangle_sum {n : ℕ} (a : Fin n → ℝ) : |∑ i, a i| ≤ ∑ i, |a i| :=
  Finset.abs_sum_le_sum_abs a Finset.univ

/-- Cauchy–Schwarz / QM–AM: `(∑ aᵢ)² ≤ n ∑ aᵢ²`.
The nonnegativity hypothesis `ha` is not needed for this inequality, but it is kept
since it was part of the requested statement. -/
