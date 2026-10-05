/-
# Psi Two Le
Category: Frontier Wave 2 (deeper machinery)
Target: Chebyshev.psi_two_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

/-- Λ(1) = 0. -/
theorem vonMangoldt_one : Λ 1 = 0 := by simp

/-- Λ(2) = log 2. -/
theorem vonMangoldt_two : Λ 2 = Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- Λ(3) = log 3. -/
theorem vonMangoldt_three : Λ 3 = Real.log 3 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  norm_num

/-- Λ(4) = log 2, since 4 = 2². -/
theorem vonMangoldt_four : Λ 4 = Real.log 2 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The second Chebyshev function at 4:
`ψ(4) = ∑_{n ≤ 4} Λ(n) = log 2 + log 3 + log 2 = log 12`. -/
theorem psi_two_le : ∑ n ∈ Finset.Icc 1 4, Λ n = Real.log 12 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  rw [show ((12 : ℝ)) = 2 * (3 * 2) by norm_num,
    Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  norm_num [vonMangoldt_one, vonMangoldt_two, vonMangoldt_three, vonMangoldt_four]

end Chebyshev

