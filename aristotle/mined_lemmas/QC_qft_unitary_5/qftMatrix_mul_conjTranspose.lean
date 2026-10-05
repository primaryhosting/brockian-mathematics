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

theorem qftMatrix_mul_conjTranspose (N : ℕ) (hN : 0 < N) :
    qftMatrix N * (qftMatrix N)ᴴ = 1 := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  ext j k
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, Matrix.one_apply, Complex.star_def]
  have hterm : ∀ m : Fin N, qftMatrix N j m * (starRingEnd ℂ) (qftMatrix N k m)
      = ((N : ℂ))⁻¹ *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I
          * ((((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) : ℤ) : ℂ) / (N : ℂ))) ^ (m : ℕ) := by
    intro m
    rw [qftMatrix_mul_conj_entry N j k m]
    congr 1
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [← Finset.mul_sum]
  set d : ℤ := ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) with hd
  have hsum : (∑ m : Fin N,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ (m : ℕ))
      = ∑ m ∈ Finset.range N,
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ m :=
    Fin.sum_univ_eq_sum_range
      (fun m => (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) / (N : ℂ))) ^ m) N
  rw [hsum]
  by_cases hjk : j = k
  · subst hjk
    have hd0 : d = 0 := by simp [hd]
    rw [hd0]
    simp [inv_mul_cancel₀ hNc]
  · have hd0 : d ≠ 0 := by
      simp only [hd, sub_ne_zero, ne_eq, Nat.cast_inj]
      exact fun h => hjk (Fin.ext h)
    have hlt : d.natAbs < N := by
      have hj := j.isLt
      have hk := k.isLt
      simp only [hd]
      omega
    rw [sum_exp_eq_zero N hN d hd0 hlt]
    simp [hjk]

/-- **The 5-qubit QFT matrix is unitary.** -/
