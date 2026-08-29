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

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

theorem omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  field_simp at hn
  have hz : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

/-- The fifth roots of unity sum to zero. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  rw [geom_sum_eq omega_ne_one 5, omega_pow_five]
  simp

/-- Orthogonality in the base case: the character values sum to zero. -/
theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  have hfin : ∑ x : ZMod 5, e x = ∑ x : Fin 5, omega ^ (x : ℕ) := rfl
  rw [hfin, ← sum_omega_pow, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, Fin.sum_univ_five]
  norm_num

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` equals `5` when `a = 0` and `0` otherwise. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases ha : a = 0
  · subst ha
    simp [e, ZMod.val_zero]
  · rw [if_neg ha, ← sum_e]
    exact Fintype.sum_bijective _ (Equiv.mulLeft₀ a ha).bijective _ _ (fun _ => rfl)

end Characters5
end Brockian

