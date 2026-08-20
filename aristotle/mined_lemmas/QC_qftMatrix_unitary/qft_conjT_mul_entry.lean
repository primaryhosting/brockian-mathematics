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

private lemma qft_conjT_mul_entry (N : ℕ) (hN : 0 < N) (i j k : Fin N) :
    (qftMatrix N)ᴴ i k * qftMatrix N k j
      = Complex.exp
          (2 * Real.pi * Complex.I * ((k : ℕ) * (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) : ℤ)) / N) / N := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = (N : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  have hc : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℂ) * ((i : ℕ) : ℂ)) / N)
      = -(2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℂ) * ((i : ℕ) : ℂ)) / N) := by
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.conj_natCast]
    ring
  rw [Matrix.conjTranspose_apply, Complex.star_def]
  simp only [qftMatrix, map_div₀, Complex.conj_ofReal, ← Complex.exp_conj, hc]
  rw [div_mul_div_comm, ← Complex.exp_add, hsq]
  congr 1
  push_cast
  field_simp
  ring_nf

/-- The `N × N` quantum Fourier transform matrix is unitary, for every `N > 0`. -/
