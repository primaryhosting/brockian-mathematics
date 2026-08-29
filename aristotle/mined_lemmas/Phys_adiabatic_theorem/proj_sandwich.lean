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

lemma proj_sandwich (hproj : ∀ s, P s * P s = P s)
    (hP : ∀ s, HasDerivAt P (P' s) s) (s : ℝ) :
    P s * P' s * P s = 0 := by
  have h := proj_deriv_leibniz hproj hP s
  have h2 := congrArg (fun X => P s * X) h
  simp only [mul_add, ← mul_assoc, hproj] at h2
  -- h2 : P s * P' s * P s + P s * P' s = P s * P' s
  have := h2
  linear_combination (norm := module) this

/-- The key algebraic identity behind the adiabatic theorem:
the derivative of the projection is the commutator of the Kato generator with the projection. -/
