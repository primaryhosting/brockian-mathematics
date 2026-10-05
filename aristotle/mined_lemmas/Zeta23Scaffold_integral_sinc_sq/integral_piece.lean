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

lemma integral_piece (c : ℝ) (hc : c ≠ 0) (a b x y : ℝ) :
    ∫ v in x..y, ee c v * ((a + b * v : ℝ) : ℂ) = antid c a b y - antid c a b x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hasDerivAt_antid c hc a b v)
  exact Continuous.intervalIntegrable ((continuous_ee c).mul (by fun_prop)) _ _

