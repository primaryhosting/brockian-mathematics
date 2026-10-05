/-
# Mobius Root Sum 10
Category: Pure Mathematics
Target: Math.mobius_root_sum_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial

namespace Math

/-- The tenth cyclotomic polynomial over `ℂ` is `X^4 - X^3 + X^2 - X + 1`. -/

theorem cyclotomic_ten_complex :
    cyclotomic 10 ℂ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  have h := prod_cyclotomic_eq_X_pow_sub_one (n := 10) (by norm_num) ℂ
  have hd : (10 : ℕ).divisors = {1, 2, 5, 10} := by decide
  rw [hd] at h
  have h5 : cyclotomic 5 ℂ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [cyclotomic_prime]
    simp [Finset.sum_range_succ]
    ring
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, cyclotomic_one, cyclotomic_two, h5] at h
  have hne1 : ((X : ℂ[X]) - 1) ≠ 0 := by
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 1) h0
    simp [Polynomial.coeff_one] at this
  have hne2 : ((X : ℂ[X]) + 1) ≠ 0 := by
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 1) h0
    simp [Polynomial.coeff_one] at this
  have hne5 : ((X : ℂ[X]) ^ 4 + X ^ 3 + X ^ 2 + X + 1) ≠ 0 := by
    intro h0
    have := congrArg (fun p => Polynomial.coeff p 0) h0
    simp at this
  have key : ((X : ℂ[X]) - 1) * ((X + 1) * ((X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * cyclotomic 10 ℂ))
      = (X - 1) * ((X + 1) *
          ((X ^ 4 + X ^ 3 + X ^ 2 + X + 1) * (X ^ 4 - X ^ 3 + X ^ 2 - X + 1))) := by
    rw [h]; ring
  exact mul_left_cancel₀ hne5 (mul_left_cancel₀ hne2 (mul_left_cancel₀ hne1 key))

/-- The Möbius function at `10` equals `1`. -/
