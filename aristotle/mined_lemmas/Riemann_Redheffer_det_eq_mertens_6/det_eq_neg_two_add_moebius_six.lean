import Mathlib
/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Riemann
namespace Redheffer

/-- The `6 × 6` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`,
and `R i j = 0` otherwise. -/

theorem det_eq_neg_two_add_moebius_six :
    R.det = -2 + ArithmeticFunction.moebius 6 := by
  have h6 : (6 : ℕ) = 2 * 3 := by norm_num
  have h : ArithmeticFunction.moebius 6 = 1 := by
    rw [h6, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num),
      ArithmeticFunction.moebius_apply_prime (by norm_num)]
    norm_num
  rw [det_eq_mertens_6, h]
  norm_num

end Redheffer
end Riemann

