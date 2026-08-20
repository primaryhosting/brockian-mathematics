import Mathlib

/-!
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ` (0-indexed): the entry in row `i`, column `j`
is `1` when `j = 0` or when `i + 1` divides `j + 1`, and `0` otherwise. -/

theorem det_eq_mertens_sum_5 :
    R5.det = ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ) := by
  have h4 : ArithmeticFunction.moebius 4 = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
    decide
  rw [det_eq_mertens_5]
  simp [Finset.sum_Icc_succ_top, ArithmeticFunction.moebius_apply_prime,
    show Nat.Prime 2 by norm_num, show Nat.Prime 3 by norm_num, show Nat.Prime 5 by norm_num, h4]

end Riemann.Redheffer

