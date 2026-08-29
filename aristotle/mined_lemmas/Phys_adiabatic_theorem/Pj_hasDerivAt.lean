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

lemma Pj_hasDerivAt (s : ℝ) : HasDerivAt Pj (Pj' s) s := by
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2*t)) (-Real.sin (2*s) * 2) s := by
    simpa using (Real.hasDerivAt_cos (2*s)).comp s ((hasDerivAt_id s).const_mul 2)
  have hs : HasDerivAt (fun t : ℝ => Real.sin (2*t)) (Real.cos (2*s) * 2) s := by
    simpa using (Real.hasDerivAt_sin (2*s)).comp s ((hasDerivAt_id s).const_mul 2)
  have h1 : HasDerivAt (fun t : ℝ => ((Real.cos (2*t) : ℝ) : ℂ) • sigma3)
      ((((-Real.sin (2*s) * 2 : ℝ)) : ℂ) • sigma3) s := hc.ofReal_comp.smul_const _
  have h2 : HasDerivAt (fun t : ℝ => ((Real.sin (2*t) : ℝ) : ℂ) • sigma1)
      ((((Real.cos (2*s) * 2 : ℝ)) : ℂ) • sigma1) s := hs.ofReal_comp.smul_const _
  have h3 := ((hasDerivAt_const s (1 : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))).add h1).add h2
  have h4 := h3.const_smul ((2:ℂ)⁻¹)
  have : Pj' s = (2:ℂ)⁻¹ • ((0 + (((-Real.sin (2*s) * 2 : ℝ)) : ℂ) • sigma3)
      + (((Real.cos (2*s) * 2 : ℝ)) : ℂ) • sigma1) := by
    simp only [Pj', zero_add]
    norm_num [mul_comm]
  rw [this]
  exact h4

