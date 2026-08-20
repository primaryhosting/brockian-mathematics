/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Riemann.Redheffer

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, else `0`. -/

theorem mertens_four : mertens 4 = -1 := by
  rw [mertens, show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide : ¬ Squarefree 4)]

/-- The determinant of the 4×4 Redheffer matrix is `-1`, which equals the Mertens
function value `M(4)`. -/
