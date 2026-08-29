/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

set_option pp.fullNames false

namespace Phys

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's geometric generator `K(s) = [P'(s), P(s)] = P'(s)P(s) - P(s)P'(s)` associated with a
differentiable family of spectral projections `P` with derivative `dP`. -/

theorem adiabaticGenerator_intertwine (hPP : ∀ s, P s * P s = P s)
    (hdP : ∀ s, HasDerivAt P (dP s) s)
    (hHP : ∀ s, H s * P s = ev s • P s) (hPH : ∀ s, P s * H s = ev s • P s) (s : ℝ) :
    dP s + P s * adiabaticGenerator τ H P dP s
      = adiabaticGenerator τ H P dP s * P s := by
  have hd := deriv_proj_eq hPP hdP s
  have hsand := proj_sandwich_eq_zero hPP hdP s
  have hsq := hPP s
  have hsq2 : dP s * P s * P s = dP s * P s := by rw [mul_assoc, hsq]
  simp only [adiabaticGenerator, katoGenerator, mul_add, mul_sub, add_mul, sub_mul,
    mul_smul_comm, smul_mul_assoc, ← mul_assoc, hPH, hHP, hsq, hsq2, hsand]
  set a := dP s * P s with ha
  set b := P s * dP s with hb
  rw [hd]
  abel

variable (H P dP U ev τ) in
/-- The intertwining relation `P(s) U(s) = U(s) P(0)` for the adiabatic evolution `U`:
the adiabatic propagator maps the initial spectral subspace onto the instantaneous one. -/
