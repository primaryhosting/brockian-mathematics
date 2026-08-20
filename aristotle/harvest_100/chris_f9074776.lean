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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul,
    show (5 : ℕ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma omega_ne_one : omega ≠ 1 := by
  intro h
  rw [omega, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have hone : (1 : ℂ) = 5 * n :=
    mul_right_cancel₀ h2 (by linear_combination (5 : ℂ) * hn)
  have hn5 : (5 : ℤ) * n = 1 := by exact_mod_cast hone.symm
  omega

lemma sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  rw [geom_sum_eq omega_ne_one, omega_pow_five]
  simp

lemma sum_e : ∑ x : ZMod 5, e x = 0 := by
  have h : ∑ x : ZMod 5, e x = ∑ k ∈ Finset.range 5, omega ^ k := by
    simp [e, Fin.sum_univ_five, ZMod, Finset.sum_range_succ, ZMod.val]
  rw [h, sum_omega_pow]

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` is `5` when `a = 0` and `0` otherwise. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [e]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h : ∑ x : ZMod 5, e (a * x) = ∑ x : ZMod 5, e x :=
      Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun _ => rfl)
    rw [h, sum_e, if_neg ha]

end Brockian.Characters5

