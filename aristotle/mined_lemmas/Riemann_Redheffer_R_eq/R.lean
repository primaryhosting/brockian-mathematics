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

def R : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0

/-- Explicit entries of the 4×4 Redheffer matrix. -/
