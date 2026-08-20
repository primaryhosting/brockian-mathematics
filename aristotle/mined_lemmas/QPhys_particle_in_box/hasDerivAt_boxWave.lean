import Mathlib

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

namespace QPhys

/-- The `n`-th energy level of a particle of mass `m` in an infinite square well of width `L`:
`E_n = n² π² ℏ² / (2 m L²)`. -/

lemma hasDerivAt_boxWave (L : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (boxWave L n) (boxWaveD1 L n x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * Real.pi / L * y) ((n : ℝ) * Real.pi / L) x := by
    simpa using (hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi / L)
  have h2 := (Real.hasDerivAt_sin ((n : ℝ) * Real.pi / L * x)).comp x h1
  have h3 := h2.const_mul (Real.sqrt (2 / L))
  refine h3.congr_deriv ?_
  simp only [boxWaveD1]
  ring

/-- `boxWaveD2 L n` is the derivative of `boxWaveD1 L n`. -/
