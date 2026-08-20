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
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma sum_omegaN_zpow (N : ℕ) (hN : N ≠ 0) (d : ℤ) :
    ∑ m ∈ Finset.range N, (omegaN N ^ d) ^ m = if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  have hprim := isPrimitiveRoot_omegaN N hN
  have hpow : (omegaN N ^ d) ^ N = 1 := by
    rw [← zpow_natCast (omegaN N ^ d) N, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, IsPrimitiveRoot.pow_eq_one hprim, _root_.one_zpow]
  by_cases hd : (N : ℤ) ∣ d
  · have hz : omegaN N ^ d = 1 := (hprim.zpow_eq_one_iff_dvd d).mpr hd
    simp [hz, hd]
  · have hz : omegaN N ^ d ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
    rw [geom_sum_eq hz, hpow, if_neg hd]
    simp

/-- The `N`-dimensional discrete Fourier transform matrix is unitary. -/
