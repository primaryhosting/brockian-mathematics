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

set_option maxHeartbeats 1000000

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`, valued in `ℂ`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma omega_pow_five : omega ^ 5 = 1 := by
  have h : omega ^ (5 : ℕ) = Complex.exp ((5 : ℕ) * (2 * Real.pi * Complex.I / 5)) := by
    rw [omega, ← Complex.exp_nat_mul]
  rw [h]
  have h5 : ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [h5]
  simp

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  field_simp [h2] at hn
  have hz : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

lemma sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  have hfac : (omega - 1) * (∑ k ∈ Finset.range 5, omega ^ k) = omega ^ 5 - 1 := by
    simp [Finset.sum_range_succ]
    ring
  rw [omega_pow_five, sub_self] at hfac
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) omega_ne_one
  · exact h

lemma sum_e : ∑ x : ZMod 5, e x = 0 := by
  have h : ∑ x : ZMod 5, e x = ∑ k ∈ Finset.range 5, omega ^ k := by
    show ∑ x : Fin 5, omega ^ (x : ℕ) = _
    simp [Fin.sum_univ_five, Finset.sum_range_succ]
  rw [h, sum_omega_pow]

/-- Additive-character orthogonality on `ZMod 5`. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases ha : a = 0
  · subst ha
    simp [e]
  · rw [if_neg ha]
    have hbij : ∑ x : ZMod 5, e (a * x) = ∑ x : ZMod 5, e x :=
      Equiv.sum_comp (Equiv.mulLeft₀ a ha) e
    rw [hbij, sum_e]

end Characters5
end Brockian

#print axioms Brockian.Characters5.sum_e_mul

