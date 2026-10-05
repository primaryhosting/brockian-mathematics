/-
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
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

namespace Chebyshev

open ArithmeticFunction

/-- `Λ 4 = log 2`, since `4 = 2 ^ 2` is a prime power with smallest prime factor `2`. -/

theorem psi_two_le : ∑ n ∈ Finset.Icc 1 4, Λ n = Real.log 12 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
  simp [vonMangoldt_apply_one, vonMangoldt_apply_prime Nat.prime_two,
    vonMangoldt_apply_prime Nat.prime_three, vonMangoldt_four]
  rw [show (12 : ℝ) = 2 * 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  ring

end Chebyshev

#print axioms Chebyshev.psi_two_le

