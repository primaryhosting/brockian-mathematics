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

theorem proj_sandwich_eq_zero (hPP : ∀ s, P s * P s = P s) (hdP : ∀ s, HasDerivAt P (dP s) s)
    (s : ℝ) : P s * dP s * P s = 0 := by
  have hd := deriv_proj_eq hPP hdP s
  have hsq := hPP s
  have e : P s * dP s * P s = P s * dP s * P s + P s * dP s * P s := by
    calc P s * dP s * P s = P s * (dP s * P s + P s * dP s) * P s := by rw [← hd]
      _ = P s * dP s * (P s * P s) + (P s * P s) * dP s * P s := by noncomm_ring
      _ = P s * dP s * P s + P s * dP s * P s := by rw [hsq]
  simpa using sub_eq_zero_of_eq e

/-- The key algebraic intertwining identity: `P' + P G = G P`, where `G` is the adiabatic
generator.  This is what makes the adiabatic evolution preserve the instantaneous eigenspaces. -/
