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

set_option grind.warning false

namespace QC

/-- The `N × N` quantum Fourier transform matrix:
`(QFT_N)_{j,k} = N^{-1/2} · exp(2πi·jk/N)`. -/

theorem qftMatrix_mul_conj_entry (N : ℕ) (j k m : Fin N) :
    qftMatrix N j m * (starRingEnd ℂ) (qftMatrix N k m)
      = ((N : ℂ))⁻¹ *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((j : ℕ) : ℂ) - ((k : ℕ) : ℂ))
          * ((m : ℕ) : ℂ) / (N : ℂ)) := by
  have hN : 0 < N := Fin.pos j
  have hs : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = ((N : ℂ))⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_num
  simp only [qftMatrix, Matrix.of_apply, map_mul, ← Complex.exp_conj]
  rw [show ((starRingEnd ℂ) ((Real.sqrt N : ℂ))⁻¹) = ((Real.sqrt N : ℂ))⁻¹ by
    simp [← Complex.ofReal_inv]]
  rw [mul_mul_mul_comm, hs, ← Complex.exp_add]
  congr 1
  have h2 : ((starRingEnd ℂ)
      (2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) * (m : ℕ) : ℕ) : ℂ) / (N : ℂ)))
      = -(2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℂ) * ((m : ℕ) : ℂ)) / (N : ℂ)) := by
    push_cast
    simp [Complex.ext_iff]
    ring
  rw [h2]
  push_cast
  congr 1
  have h : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp
  ring

/-- If `d` is a nonzero integer of absolute value less than `N`, then `exp(2πi d/N) ≠ 1`. -/
