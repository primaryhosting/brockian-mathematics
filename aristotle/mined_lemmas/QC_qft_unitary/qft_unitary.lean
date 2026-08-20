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

namespace QC

open Complex Finset

/-- The `n`-qubit quantum Fourier transform matrix, of size `2 ^ n × 2 ^ n`:
`(QFT)_{j,k} = (1 / √(2^n)) * exp (2 π i j k / 2^n)`. -/

theorem qft_unitary (n : ℕ) : qft n ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have hN : 0 < 2 ^ n := Nat.two_pow_pos n
  have hNR : (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by positivity
  have hsq : ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹ * ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹
      = (((2 ^ n : ℕ) : ℂ))⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hNR]
    push_cast
    ring
  have hNc : ((2 ^ n : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hN.ne'
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hstep : ∀ k : Fin (2 ^ n), qft n j k * (star (qft n)) k l
      = ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹ * ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹ *
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((j : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
            ((2 ^ n : ℕ) : ℂ)) *
          (starRingEnd ℂ)
            (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((l : ℕ) : ℂ) * ((k : ℕ) : ℂ) /
              ((2 ^ n : ℕ) : ℂ)))) := by
    intro k
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, qft, map_mul,
      Complex.conj_ofReal, map_inv₀, Complex.star_def, map_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hstep k), ← Finset.mul_sum, qft_row_sum n j l, hsq]
  by_cases hjl : j = l
  · rw [if_pos hjl, if_pos hjl, inv_mul_cancel₀ hNc]
  · rw [if_neg hjl, if_neg hjl, mul_zero]

end QC

