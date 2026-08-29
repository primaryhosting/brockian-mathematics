/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
its `(j, k)` entry is `exp (2 π i j k / N) / √N`. -/

lemma qftMatrix_conjTranspose_mul_self (N : ℕ) (hN : 0 < N) :
    (qftMatrix N)ᴴ * qftMatrix N = 1 := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  ext j l
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_congr rfl (fun k _ => qftMatrix_conj_mul_entry N hN j l k), ← Finset.sum_div]
  by_cases hjl : j = l
  · subst hjl
    have hz : (Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) - (j : ℕ)) / N)) = 1 := by
      simp
    simp only [hz, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    rw [div_self hNne, Matrix.one_apply_eq]
  · rw [sum_root_of_unity_eq_zero N hN j l hjl, zero_div, Matrix.one_apply_ne hjl]

/-- The `N × N` quantum Fourier transform matrix is unitary. -/
