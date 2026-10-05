/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset

namespace Math

/-- A primitive 6-th root of unity `ζ` satisfies `ζ ^ 3 = -1`. -/

lemma moebius_six : (ArithmeticFunction.moebius 6 : ℤ) = 1 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- The sum of the primitive 6-th roots of unity in `ℂ` equals `μ(6)`. -/
