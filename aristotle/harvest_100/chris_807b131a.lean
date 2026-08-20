/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian.Characters5

/-- The primitive fifth root of unity `exp (2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

theorem omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul,
    show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

theorem omega_ne_one : omega ≠ 1 := by
  simp only [ne_eq, omega, Complex.exp_eq_one_iff, not_exists]
  intro n hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hn
  have hn' : (5 : ℤ) * n = 1 := by exact_mod_cast hn.symm
  omega

/-- The five fifth-roots of unity sum to zero. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  rw [geom_sum_eq omega_ne_one, omega_pow_five]
  simp

/-- A sum over `ZMod 5` as a sum over `Finset.range 5`. -/
theorem sum_zmod5 (f : ZMod 5 → ℂ) :
    ∑ x : ZMod 5, f x = ∑ k ∈ Finset.range 5, f (k : ZMod 5) := by
  rw [show (∑ x : ZMod 5, f x) = ∑ x : Fin 5, f x from rfl, Fin.sum_univ_five,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  rw [sum_zmod5, ← sum_omega_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [e, ZMod.val_natCast_of_lt hk]

/-- Additive-character orthogonality on `ZMod 5`. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [e, ZMod.card]
  · rw [if_neg ha]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hb : Function.Bijective (fun x : ZMod 5 => a * x) := (Equiv.mulLeft₀ a ha).bijective
    rw [Fintype.sum_bijective _ hb (fun x => e (a * x)) e (fun x => rfl)]
    exact sum_e

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

