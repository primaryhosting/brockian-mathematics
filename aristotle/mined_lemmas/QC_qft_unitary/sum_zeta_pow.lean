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

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma sum_zeta_pow {N : ℕ} (hN : N ≠ 0) (j l : Fin N) :
    ∑ k ∈ Finset.range N, ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k
      = if j = l then (N : ℂ) else 0 := by
  have hprim := zeta_isPrimitiveRoot hN
  by_cases h : j = l
  · subst h; simp
  · have hne : (zeta N) ^ ((j.val : ℤ) - (l.val : ℤ)) ≠ 1 := by
      simp only [ne_eq, hprim.zpow_eq_one_iff_dvd]
      intro hdvd
      have h1 : (j.val : ℤ) - (l.val : ℤ) = 0 :=
        Int.eq_zero_of_abs_lt_dvd hdvd (by
          have hj := j.isLt
          have hl := l.isLt
          rw [abs_lt]; omega)
      exact h (Fin.ext (by omega))
    have hrN : ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ N = 1 := by
      rw [← zpow_natCast (zeta N ^ _) N, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hprim.pow_eq_one, one_zpow]
    rw [geom_sum_eq hne, hrN, if_neg h]
    simp

/-- The `N`-point discrete Fourier transform matrix is unitary. -/
