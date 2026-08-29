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

import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Matrix Finset

/-- The `N × N` discrete Fourier transform matrix, with entries
`(1/√N) · exp(2πi·jk/N)`. -/

private lemma sum_zpow_eq_zero (hN : N ≠ 0) (m : ℤ) (hm : ¬ ((N : ℤ) ∣ m)) :
    ∑ j : Fin N, ((zeta N) ^ m) ^ (j : ℕ) = 0 := by
  set w : ℂ := (zeta N) ^ m with hw
  have hne : w ≠ 1 := by
    rw [hw, ne_eq, (isPrimitiveRoot_zeta hN).zpow_eq_one_iff_dvd m]
    exact hm
  have hpow : w ^ N = 1 := by
    rw [hw, ← zpow_natCast ((zeta N) ^ m) N, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, (isPrimitiveRoot_zeta hN).pow_eq_one, _root_.one_zpow]
  rw [Fin.sum_univ_eq_sum_range (fun i => w ^ i) N, geom_sum_eq hne, hpow, sub_self, zero_div]

