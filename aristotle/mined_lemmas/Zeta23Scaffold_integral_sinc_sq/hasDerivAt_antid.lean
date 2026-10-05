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

lemma hasDerivAt_antid (c : ℝ) (hc : c ≠ 0) (a b : ℝ) (v : ℝ) :
    HasDerivAt (antid c a b) (ee c v * ((a + b * v : ℝ) : ℂ)) v := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have he := hasDerivAt_ee c v
  have hlin : HasDerivAt (fun u : ℝ => ((a + b * u : ℝ) : ℂ)) (b : ℂ) v := by
    have h : HasDerivAt (fun u : ℝ => (a + b * u : ℝ)) b v := by
      simpa using ((hasDerivAt_id v).const_mul b).const_add a
    simpa using h.ofReal_comp
  have h1 := ((hlin.mul he).div_const (-(c * I))).add ((he.const_mul (b : ℂ)).div_const ((c : ℂ) ^ 2))
  convert h1 using 1
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hIne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  ring_nf
  rw [hI]
  ring

