import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

lemma sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  have h1 : omega ≠ 1 := prim.ne_one (by norm_num)
  rw [geom_sum_eq h1 5, prim.pow_eq_one]
  simp

