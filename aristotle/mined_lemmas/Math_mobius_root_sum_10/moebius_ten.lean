import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- For a primitive `n`-th root of unity `ζ`, the finset of primitive `n`-th roots of unity is
the image of the residues coprime to `n` under `i ↦ ζ ^ i`. -/

lemma moebius_ten : (ArithmeticFunction.moebius 10 : ℤ) = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- The sum of the primitive 10-th roots of unity in `ℂ` equals `μ 10`. -/
