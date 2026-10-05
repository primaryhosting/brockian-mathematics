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

open Complex Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma sum_pow_eq_zero {N : ℕ} (hN : N ≠ 0) {j l : Fin N} (hjl : j ≠ l) :
    ∑ k ∈ Finset.range N, (omegaN N ^ (j : ℕ) * (omegaN N ^ (l : ℕ))⁻¹) ^ k = 0 := by
  have hprim : IsPrimitiveRoot (omegaN N) N := isPrimitiveRoot_omegaN hN
  have hz := pow_mul_inv_pow (omegaN N) (omegaN_ne_zero N) (j : ℕ) (l : ℕ)
  have hne : omegaN N ^ ((j : ℤ) - (l : ℤ)) ≠ 1 := by
    rw [Ne, hprim.zpow_eq_one_iff_dvd]
    intro hdvd
    have habs : |((j : ℤ) - (l : ℤ))| < (N : ℤ) := by
      have hj : (j : ℤ) < N := by exact_mod_cast j.isLt
      have hl : (l : ℤ) < N := by exact_mod_cast l.isLt
      have hj0 : (0 : ℤ) ≤ (j : ℤ) := by positivity
      have hl0 : (0 : ℤ) ≤ (l : ℤ) := by positivity
      rw [abs_lt]; omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    exact hjl (Fin.ext (by omega))
  have hpow : (omegaN N ^ ((j : ℤ) - (l : ℤ))) ^ N = 1 := by
    rw [← zpow_natCast (omegaN N ^ ((j : ℤ) - (l : ℤ))) N, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hprim.pow_eq_one, one_zpow]
  rw [hz, geom_sum_eq hne, hpow, sub_self, zero_div]

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
