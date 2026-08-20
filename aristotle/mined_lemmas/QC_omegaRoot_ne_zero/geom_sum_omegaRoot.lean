/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
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

namespace QC

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma geom_sum_omegaRoot {n : ℕ} (hn : n ≠ 0) (d : ℤ) (hd : ¬ ((n : ℤ) ∣ d)) :
    ∑ j ∈ Finset.range n, (omegaRoot n ^ d) ^ j = 0 := by
  have hprim := isPrimitiveRoot_omegaRoot hn
  have hne : omegaRoot n ^ d ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
  have hpow : (omegaRoot n ^ d) ^ n = 1 := by
    rw [← zpow_natCast (omegaRoot n ^ d) n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hprim.pow_eq_one, one_zpow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

