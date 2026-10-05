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

lemma deriv_eq_commutator_katoGen (hproj : ∀ s, P s * P s = P s)
    (hP : ∀ s, HasDerivAt P (P' s) s) (s : ℝ) :
    katoGen P P' s * P s - P s * katoGen P P' s = P' s := by
  have hs := proj_sandwich hproj hP s
  have hl := proj_deriv_leibniz hproj hP s
  have hpp := hproj s
  simp only [katoGen, sub_mul, mul_sub]
  rw [mul_assoc (P' s) (P s) (P s), hpp, hs, ← mul_assoc (P s) (P' s) (P s), hs,
    ← mul_assoc (P s) (P s) (P' s), hpp]
  simp only [sub_zero, zero_sub, sub_neg_eq_add]
  exact hl

end

section

variable {P P' U : ℝ → (E →L[ℂ] E)} {phase : ℝ → ℂ}

/-- The full adiabatic generator: a scalar (dynamical / geometric phase) term plus
Kato's generator. -/
