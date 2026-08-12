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

/-- The von Mangoldt function at `4 = 2 ^ 2` equals `Real.log 2`. -/
lemma vonMangoldt_four : Λ 4 = Real.log 2 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, vonMangoldt_apply_pow (by norm_num), vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- The second Chebyshev function at `4`:
`ψ(4) = Λ 1 + Λ 2 + Λ 3 + Λ 4 = log 2 + log 3 + log 2 = log 12`. -/
theorem psi_two_le :
    ∑ n ∈ Finset.Icc 1 4, ArithmeticFunction.vonMangoldt n = Real.log 12 := by
  have h2 : Λ 2 = Real.log 2 := by
    simpa using vonMangoldt_apply_prime Nat.prime_two
  have h3 : Λ 3 = Real.log 3 := by
    simpa using vonMangoldt_apply_prime Nat.prime_three
  have hsum : ∑ n ∈ Finset.Icc 1 4, Λ n = Λ 1 + Λ 2 + Λ 3 + Λ 4 := by
    have hset : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
    rw [hset]
    simp [Finset.sum_insert, Finset.mem_insert]
    ring
  rw [hsum, h2, h3, vonMangoldt_four, vonMangoldt_apply_one]
  have : (12 : ℝ) = 2 * 3 * 2 := by norm_num
  rw [this, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  ring

end Chebyshev

