/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

open Complex

/-- The `N`-th root of unity `exp (2 π i / N)`. -/

lemma zeta_zpow_ne_one (N : ℕ) (hN : N ≠ 0) (d : ℤ) (hd : |d| < (N : ℤ)) (hd0 : d ≠ 0) :
    zeta N ^ d ≠ 1 := by
  intro h
  have hdvd : (N : ℤ) ∣ d := ((zeta_isPrimitiveRoot N hN).zpow_eq_one_iff_dvd d).mp h
  have habs : (N : ℤ) ∣ |d| := (dvd_abs _ _).mpr hdvd
  have : (N : ℤ) ≤ |d| := Int.le_of_dvd (abs_pos.mpr hd0) habs
  omega

/-- The geometric sum of powers of `ζ^d` over a full period. -/
