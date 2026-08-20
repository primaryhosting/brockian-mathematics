/-
# Mobius Root Sum 5
Category: Pure Mathematics
Target: Math.mobius_root_sum_5
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

namespace Math

open Polynomial

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The number of primitive `5`-th roots of unity in `ℂ` is `4`. -/

private lemma coeff_cyclotomic_five : ((cyclotomic 5 ℂ).coeff 3) = 1 := by
  rw [cyclotomic_prime]
  simp [Finset.sum_range_succ, coeff_one, coeff_X_pow, coeff_X]

/-- The sum of the primitive `5`-th roots of unity equals `μ 5 = -1`. -/
