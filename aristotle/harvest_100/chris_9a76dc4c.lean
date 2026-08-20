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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chebyshev

open ArithmeticFunction

/-- The von Mangoldt function at `4` equals `log 2`, since `4 = 2 ^ 2`. -/
lemma vonMangoldt_four : Λ 4 = Real.log 2 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The von Mangoldt function at `2` equals `log 2`. -/
lemma vonMangoldt_two : Λ 2 = Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The von Mangoldt function at `3` equals `log 3`. -/
lemma vonMangoldt_three : Λ 3 = Real.log 3 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  norm_num

/-- Key intermediate step: `log 2 + log 3 + log 2 = log 12`. -/
lemma log_two_add_log_three_add_log_two :
    Real.log 2 + Real.log 3 + Real.log 2 = Real.log 12 := by
  have h : (12 : ℝ) = 2 * 3 * 2 := by norm_num
  rw [h, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

/-- The second Chebyshev function at `4`:
`ψ(4) = ∑_{n ≤ 4} Λ(n) = log 2 + log 3 + log 2 = log 12`. -/
theorem psi_two_le :
    ∑ n ∈ ({1, 2, 3, 4} : Finset ℕ), Λ n = Real.log 12 := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    ArithmeticFunction.vonMangoldt_apply_one, vonMangoldt_two, vonMangoldt_three,
    vonMangoldt_four, zero_add, ← add_assoc]
  exact log_two_add_log_three_add_log_two

end Chebyshev

