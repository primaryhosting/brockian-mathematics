import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

open ArithmeticFunction

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` (first column) or if
`(i+1) ∣ (j+1)` (divisibility of the 1-based indices), and `0` otherwise. -/

theorem det_eq_mertens_4 : R.det = -1 := by
  rw [R_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- The value `-1` is indeed the Mertens function `M(4) = ∑_{n ≤ 4} μ(n)`. -/
