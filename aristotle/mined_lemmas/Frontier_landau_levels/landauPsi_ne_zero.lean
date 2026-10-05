/-
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Levels
Category: Frontier Physics
Target: Frontier.landau_levels
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

namespace Frontier

open Polynomial

/-! ## Hermite polynomials over `ℝ` -/

/-- The (probabilists') Hermite polynomials, with real coefficients. -/

theorem landauPsi_ne_zero (hbar q B k : ℝ) (n : ℕ) (hhbar : 0 < hbar) (hqB : 0 < q * B) :
    ∃ x y : ℝ, landauPsi hbar q B k n x y ≠ 0 := by
  have hL : landauL hbar q B ≠ 0 := (landauL_pos hhbar hqB).ne'
  obtain ⟨t, ht⟩ : ∃ t : ℝ, (hermiteR n).eval t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hermiteR_ne_zero n (Polynomial.funext (fun r => by simpa using h r))
  refine ⟨t * landauL hbar q B + landauX0 hbar q B k, 0, ?_⟩
  have harg : (t * landauL hbar q B + landauX0 hbar q B k - landauX0 hbar q B k)
      / landauL hbar q B = t := by
    rw [add_sub_cancel_right]
    field_simp
  simp only [landauPsi, harg, chi, F]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (Complex.ofReal_ne_zero.mpr (mul_ne_zero ht (Real.exp_ne_zero _)))

end Frontier

