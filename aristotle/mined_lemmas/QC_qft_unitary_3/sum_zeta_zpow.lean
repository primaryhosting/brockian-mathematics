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

lemma sum_zeta_zpow (N : ℕ) (hN : N ≠ 0) (d : ℤ) (hd : |d| < (N : ℤ)) :
    ∑ j : Fin N, (zeta N ^ d) ^ (j : ℕ) = if d = 0 then (N : ℂ) else 0 := by
  by_cases hd0 : d = 0
  · subst hd0
    simp
  · rw [if_neg hd0]
    have hne : zeta N ^ d ≠ 1 := zeta_zpow_ne_one N hN d hd hd0
    rw [Fin.sum_univ_eq_sum_range (fun i => (zeta N ^ d) ^ i) N, geom_sum_eq hne]
    have hpow : (zeta N ^ d) ^ N = 1 := by
      rw [← zpow_natCast (zeta N ^ d) N, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, zeta_pow_N N hN, one_zpow]
    rw [hpow, sub_self, zero_div]

/-- The QFT matrix is unitary, in any dimension `N > 0`. -/
