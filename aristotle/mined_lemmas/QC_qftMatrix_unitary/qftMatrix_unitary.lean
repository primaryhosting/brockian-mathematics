/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
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

open Complex Finset Matrix

/-- The `N × N` discrete Fourier transform (quantum Fourier transform) matrix:
`F i j = exp (2 π i · j / N) / √N`. -/

theorem qftMatrix_unitary (N : ℕ) (hN : 0 < N) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  rw [Matrix.mul_apply]
  have hentry : ∀ k : Fin N, (qftMatrix N)ᴴ i k * qftMatrix N k j
      = Complex.exp
          (2 * Real.pi * Complex.I * ((k : ℕ) * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ)) / N) / N :=
    fun k => qft_conjT_mul_entry N hN i j k
  rw [Finset.sum_congr rfl (fun k _ => hentry k), ← Finset.sum_div]
  have hm : (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)).natAbs < N := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  rw [root_sum N hN _ hm]
  by_cases hij : i = j
  · subst hij
    simp [hNC]
  · have : (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) ≠ 0 := by
      simp only [sub_ne_zero, ne_eq, Nat.cast_inj]
      exact fun h => hij (Fin.ext h.symm)
    rw [if_neg this, Matrix.one_apply_ne hij]
    simp

/-- The 8-qubit quantum Fourier transform matrix (of size `2 ^ 8 = 256`) is unitary. -/
