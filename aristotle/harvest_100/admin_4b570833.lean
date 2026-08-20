-- # Sum E Mul
-- Category: Characters
-- Target: Brockian.Characters5.sum_e_mul
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character on `ZMod 5`, `e x = ω ^ x`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma omega_pow_five : omega ^ 5 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  rw [show (5 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 5) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  simp

lemma omega_ne_one : omega ≠ 1 := by
  intro hone
  rw [omega, Complex.exp_eq_one_iff] at hone
  obtain ⟨n, hn⟩ := hone
  have hA : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h : ((5 : ℂ) * n - 1) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination (-5 : ℂ) * hn
  have h2 : (5 : ℂ) * n - 1 = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hA
  have h3 : (5 : ℤ) * n = 1 := by exact_mod_cast sub_eq_zero.mp h2
  omega

/-- The five fifth roots of unity sum to zero. -/
lemma sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 := by
  rw [geom_sum_eq omega_ne_one 5, omega_pow_five]
  simp

lemma zmod_five_cases (a : ZMod 5) : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
  revert a; decide

lemma sum_univ_zmod_five (f : ZMod 5 → ℂ) :
    ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  rw [show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Additive-character orthogonality on `ZMod 5`. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  have hs : omega ^ 0 + omega ^ 1 + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
    have h := sum_omega_pow
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one] at h
    exact h
  have h1 : (1 : ZMod 5) ≠ 0 := by decide
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have h3 : (3 : ZMod 5) ≠ 0 := by decide
  have h4 : (4 : ZMod 5) ≠ 0 := by decide
  rcases zmod_five_cases a with rfl | rfl | rfl | rfl | rfl <;>
    simp only [sum_univ_zmod_five, e] <;>
    norm_num [ZMod.val, h1, h2, h3, h4] <;>
    linear_combination hs

end Brockian.Characters5

