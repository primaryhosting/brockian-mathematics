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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology AddCircle

namespace Brockian.Equidistribution

/-- The Cesàro (Birkhoff) average of `f` along the first `N` terms of the sequence `x`. -/

lemma integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ t, (fourier k t : ℂ) ∂(haarAddCircle (T := 1)) = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) k) 0
  rw [fourierCoeff] at h
  simpa [Pi.single, Function.update, hk, eq_comm] using h

/-- Continuous functions on the circle are integrable for the Haar probability measure. -/
