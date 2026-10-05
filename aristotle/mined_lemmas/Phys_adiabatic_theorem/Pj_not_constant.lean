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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Kato's adiabatic generator associated with a smooth family of spectral projections
`P` with derivative `P'`: `K(s) = [P'(s), P(s)] = P'(s)P(s) - P(s)P'(s)`. -/

lemma Pj_not_constant : Pj 0 ≠ Pj (Real.pi / 4) := by
  intro h
  have h2 := congrArg (fun T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => T (1, 0)) h
  rw [show (2 : ℝ) * (Real.pi / 4) = Real.pi / 2 by ring] at h2
  simp [Pj, sigma3, sigma1, Prod.ext_iff] at h2
  norm_num at h2

/-- The propagated state is never zero. -/
