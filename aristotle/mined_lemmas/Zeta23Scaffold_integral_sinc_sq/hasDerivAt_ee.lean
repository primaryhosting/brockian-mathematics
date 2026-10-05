import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
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

namespace Zeta23Scaffold

open MeasureTheory Real Complex
open scoped FourierTransform

/-! ### The triangular (tent) function and its Fourier transform -/

/-- The tent function `t ↦ max (1 - |t|) 0`, real valued. -/

lemma hasDerivAt_ee (c v : ℝ) : HasDerivAt (fun u : ℝ => ee c u) (-(c * I) * ee c v) v := by
  have h0 : HasDerivAt (fun u : ℝ => (-(c * u) : ℝ)) (-c) v := by
    simpa using ((hasDerivAt_id v).const_mul (-c))
  have h : HasDerivAt (fun u : ℝ => ((-(c * u) : ℝ) : ℂ) * I) (-(c * I)) v := by
    simpa [mul_comm] using (h0.ofReal_comp.mul_const I)
  simpa [ee, mul_comm] using h.cexp

