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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian
namespace Characters5

open Complex

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`, written via `omega`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem e_eq_stdAddChar (x : ZMod 5) : e x = ZMod.stdAddChar x := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, e, omega, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

theorem omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = (2 * Real.pi * Complex.I) by
    push_cast; ring]
  simp

theorem omega_ne_one : omega ≠ 1 := by
  intro hone
  rw [omega, Complex.exp_eq_one_iff] at hone
  obtain ⟨n, hn⟩ := hone
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have key : ((1 : ℂ) - 5 * n) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination (5 : ℂ) * hn
  rcases mul_eq_zero.mp key with h | h
  · have h' : (5 : ℂ) * n = 1 := by linear_combination -h
    have : (5 : ℤ) * n = 1 := by exact_mod_cast h'
    omega
  · exact h2pi h

/-- The sum of all fifth roots of unity vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  rw [geom_sum_eq omega_ne_one 5, omega_pow_five, sub_self, zero_div]

theorem sum_e_mul (a : ZMod 5) :
    ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  classical
  simp_rw [e_eq_stdAddChar, mul_comm a]
  rw [AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar 5), ZMod.card]
  norm_num

end Characters5
end Brockian

