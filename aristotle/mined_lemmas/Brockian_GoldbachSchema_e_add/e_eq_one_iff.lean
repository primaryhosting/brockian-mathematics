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

lemma e_eq_one_iff (x : ℝ) : e x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold e
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have hx : (x : ℂ) = (j : ℂ) :=
      mul_left_cancel₀ h2
        (by linear_combination hj : (2 : ℂ) * Real.pi * Complex.I * (x : ℂ)
              = 2 * Real.pi * Complex.I * (j : ℂ))
    exact_mod_cast hx
  · rintro ⟨j, rfl⟩
    exact ⟨j, by push_cast; ring⟩

/-- Discrete orthogonality of additive characters modulo `N`. -/
