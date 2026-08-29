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

theorem dft_unitary {N : ℕ} (hN : N ≠ 0) : dftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply]
  have hsum : ∑ k : Fin N, dftMatrix N j k * star (dftMatrix N) k l
      = (∑ k ∈ Finset.range N, ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k) / (N : ℂ) := by
    rw [Finset.sum_div,
      ← Fin.sum_univ_eq_sum_range
        (fun k => ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k / (N : ℂ)) N]
    exact Finset.sum_congr rfl fun k _ => dft_mul_star_term j l k
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [hsum, sum_zeta_pow hN]
  by_cases h : j = l <;> simp [h, Matrix.one_apply, hNC]

/-- The `n`-qubit quantum Fourier transform matrix is unitary. -/
