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

/-- The second Chebyshev function evaluated at `4`:
`ψ(4) = ∑_{n = 1}^{4} Λ n = Λ 1 + Λ 2 + Λ 3 + Λ 4 = 0 + log 2 + log 3 + log 2 = log 12`,
where `Λ` is Mathlib's `ArithmeticFunction.vonMangoldt`.

The individual values come from `ArithmeticFunction.vonMangoldt_apply_one`,
`ArithmeticFunction.vonMangoldt_apply_prime` and `ArithmeticFunction.vonMangoldt_apply_pow`. -/
theorem psi_two_le :
    ∑ n ∈ Finset.Icc 1 4, ArithmeticFunction.vonMangoldt n = Real.log 12 := by
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    have h : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 := by
    simpa using ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  have hlog : Real.log 12 = Real.log 2 + Real.log 3 + Real.log 2 := by
    rw [show (12 : ℝ) = 2 * 3 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  rw [hIcc, hlog]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one, h2, h3, h4]
  ring

end Chebyshev

