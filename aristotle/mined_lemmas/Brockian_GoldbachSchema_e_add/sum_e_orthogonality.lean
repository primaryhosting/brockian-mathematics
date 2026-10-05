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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.GoldbachSchema

noncomputable section

/-- The additive character `e(x) = exp(2πi x)` on the circle. -/

lemma sum_e_orthogonality (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ k ∈ Finset.range N, e ((m * k : ℤ) / (N : ℝ)) =
      if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hNR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hterm : ∀ k ∈ Finset.range N,
      e (((m * k : ℤ) : ℝ) / (N : ℝ)) = (e ((m : ℝ) / N)) ^ k := by
    intro k _
    rw [← e_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨j, hj⟩ := hdvd
    have hx : ((m : ℤ) : ℝ) / (N : ℝ) = (j : ℝ) := by
      subst hj; push_cast; field_simp
    rw [hx, e_int, if_pos ⟨j, hj⟩]
    simp
  · have hz : e ((m : ℝ) / N) ≠ 1 := by
      intro h
      rw [e_eq_one_iff] at h
      obtain ⟨j, hj⟩ := h
      apply hdvd
      refine ⟨j, ?_⟩
      have hm : (m : ℝ) = (N : ℝ) * j := by field_simp at hj; linarith [hj]
      exact_mod_cast hm
    rw [geom_sum_eq hz]
    have hpow : (e ((m : ℝ) / N)) ^ N = 1 := by
      rw [← e_nat_mul]
      have h2 : (N : ℝ) * ((m : ℝ) / N) = ((m : ℤ) : ℝ) := by field_simp
      rw [h2, e_int]
    rw [hpow, if_neg hdvd]
    simp

/-- The exponential sum over the primes not exceeding `n`
(the "spectral" side of the circle-method model). -/
