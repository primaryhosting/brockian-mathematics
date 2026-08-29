/-
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 4
Category: Pure Mathematics
Target: Math.mobius_root_sum_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Math

open Finset Complex

/-- `Complex.I` is a primitive 4-th root of unity. -/

theorem isPrimitiveRoot_neg_I : IsPrimitiveRoot (-Complex.I) 4 := by
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by simp [pow_succ, Complex.I_mul_I]) ?_
  intro l hl hlt
  interval_cases l <;>
    norm_num [pow_succ, Complex.I_mul_I, Complex.ext_iff]

/-- The primitive 4-th roots of unity in `ℂ` are exactly `I` and `-I`. -/
