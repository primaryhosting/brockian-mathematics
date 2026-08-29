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

lemma katoGen_Pj (s : ℝ) : Phys.katoGen Pj Pj' s = -(sigma3 * sigma1) := by
  refine katoGen_of_pauli _ _ _ _ _ _ sigma3_sq sigma1_sq sigma_anticomm ?_
  have h : ((-2 * Real.sin (2*s) : ℝ) : ℂ) * ((Real.sin (2*s) : ℝ) : ℂ)
      - ((Real.cos (2*s) : ℝ) : ℂ) * ((2 * Real.cos (2*s) : ℝ) : ℂ)
      = ((-2 * (Real.sin (2*s) ^ 2 + Real.cos (2*s) ^ 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Real.sin_sq_add_cos_sq]
  norm_num

