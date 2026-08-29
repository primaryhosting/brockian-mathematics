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
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Complex MeasureTheory intervalIntegral
open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Phases -/

/-- The unimodular phase `u ↦ exp (i r u)`. -/

theorem cphase_hasDerivAt (r s : ℝ) :
    HasDerivAt (cphase r) (cphase r s * ((r : ℂ) * Complex.I)) s := by
  have h0 : HasDerivAt (fun s : ℝ => r * s) r s := by simpa using (hasDerivAt_id s).const_mul r
  have h1 : HasDerivAt (fun s : ℝ => ((r * s : ℝ) : ℂ)) (r : ℂ) s := by
    have := (Complex.ofRealCLM.hasDerivAt (x := r * s)).scomp s h0
    simp only [Complex.ofRealCLM_apply, Function.comp_def] at this
    simpa using this
  exact (h1.mul_const Complex.I).cexp

