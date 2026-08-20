import Mathlib

/-!
# Sum Omega Pow
Category: Characters
Target: Brockian.Characters5.sum_omega_pow
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

local notation "ω" => omega

theorem isPrimitiveRoot_omega : IsPrimitiveRoot ω 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega, mul_comm, mul_left_comm, mul_assoc] using h

theorem omega_pow_five : ω ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  have := isPrimitiveRoot_omega.eq_orderOf
  rw [h] at this
  simp at this

theorem sum_omega_pow : ∑ k ∈ Finset.range 5, ω ^ k = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

end Characters5
end Brockian

