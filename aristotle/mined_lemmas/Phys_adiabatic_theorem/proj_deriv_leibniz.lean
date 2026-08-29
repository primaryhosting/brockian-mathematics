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

lemma proj_deriv_leibniz (hproj : ∀ s, P s * P s = P s)
    (hP : ∀ s, HasDerivAt P (P' s) s) (s : ℝ) :
    P' s * P s + P s * P' s = P' s := by
  have h1 : HasDerivAt (fun t => P t * P t) (P' s * P s + P s * P' s) s := (hP s).mul (hP s)
  have h2 : HasDerivAt (fun t => P t * P t) (P' s) s := by
    simpa only [hproj] using hP s
  exact h1.unique h2

/-- The sandwich `P P' P` vanishes for a family of projections. -/
