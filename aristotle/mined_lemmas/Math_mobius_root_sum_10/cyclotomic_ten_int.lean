/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` commands to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
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

namespace Math

open Polynomial

/-- The tenth cyclotomic polynomial over `ℤ` is `X ^ 4 - X ^ 3 + X ^ 2 - X + 1`. -/

theorem cyclotomic_ten_int : cyclotomic 10 ℤ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : cyclotomic 5 ℤ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
    rw [cyclotomic_prime]
    simp [Finset.sum_range_succ]
    ring
  refine ((eq_cyclotomic_iff (R := ℤ) (n := 10) (by norm_num) _).mpr ?_).symm
  have h : Nat.properDivisors 10 = {1, 2, 5} := by decide
  rw [h]
  simp [cyclotomic_one, h5]
  ring

/-- The tenth cyclotomic polynomial over `ℂ`. -/
