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

theorem R_eq : R = !![1, 1, 1, 1; 1, 1, 0, 1; 1, 0, 1, 0; 1, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R]

/-- The determinant of the 4×4 Redheffer matrix equals the Mertens function
`M(4) = μ(1) + μ(2) + μ(3) + μ(4) = 1 - 1 - 1 + 0 = -1`. -/
