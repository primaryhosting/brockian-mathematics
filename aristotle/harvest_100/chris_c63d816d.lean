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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`, `e x = ω ^ x`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  push_cast
  rw [show (5 : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by ring]
  exact Complex.exp_two_pi_mul_I

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h5 : (1 : ℂ) = 5 * (n : ℂ) := by
    field_simp at hn
    exact hn
  have : (1 : ℤ) = 5 * n := by exact_mod_cast h5
  omega

/-- The sum of all fifth roots of unity vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  rw [geom_sum_eq omega_ne_one, omega_pow_five]
  simp

theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  show ∑ x : ZMod 5, omega ^ x.val = 0
  have : ∑ x : ZMod 5, omega ^ x.val = ∑ k ∈ Finset.range 5, omega ^ k := rfl
  rw [this, sum_omega_pow]

theorem e_zero : e 0 = 1 := by
  simp [e]

/-- Additive-character orthogonality on `ZMod 5`. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [e_zero]
  · rw [if_neg ha]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h := Equiv.sum_comp (Equiv.mulLeft₀ a ha) e
    simpa [Equiv.mulLeft₀, sum_e] using h

end Brockian.Characters5

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

