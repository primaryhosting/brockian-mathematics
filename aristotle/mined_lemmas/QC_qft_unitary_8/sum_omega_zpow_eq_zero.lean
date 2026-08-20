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

/-- The primitive `n`-th root of unity `exp (2πi / n)` used by the discrete Fourier transform. -/

lemma sum_omega_zpow_eq_zero (n : ℕ) (hn : n ≠ 0) (d : ℤ) (hd : ¬ ((n : ℤ) ∣ d)) :
    ∑ i ∈ Finset.range n, (omega n ^ d) ^ i = 0 := by
  have hprim : IsPrimitiveRoot (omega n) n := isPrimitiveRoot_omega n hn
  have hne : omega n ^ d ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
  have hpow : (omega n ^ d) ^ n = 1 := by
    rw [← zpow_natCast (omega n ^ d) n, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hprim.pow_eq_one, one_zpow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- The `n`-dimensional QFT matrix is unitary, for every `n ≠ 0`. -/
