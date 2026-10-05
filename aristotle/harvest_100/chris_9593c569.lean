/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
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

namespace QC

/-- The `n`-dimensional quantum Fourier transform matrix:
`(QFT_n)_{j k} = exp(2πi·jk/n) / √n`. -/
noncomputable def qft (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k =>
    (Real.sqrt n : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) * (k : ℕ)) / n)

/-- The sum of the `n`-th roots of unity raised to a fixed integer power `d` vanishes,
provided `n ∤ d`. -/
lemma sum_root_pow (n : ℕ) (hn : 0 < n) (d : ℤ) (hd : ¬ ((n : ℤ) ∣ d)) :
    ∑ l ∈ Finset.range n, Complex.exp (2 * Real.pi * Complex.I * (l * d) / n) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * d / n) with hx
  have hterm : ∀ l ∈ Finset.range n,
      Complex.exp (2 * Real.pi * Complex.I * (l * d) / n) = x ^ l := by
    intro l _
    rw [hx, ← Complex.exp_nat_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hxn : x ^ n = 1 := by
    rw [hx, ← Complex.exp_nat_mul]
    have h : (n : ℂ) * (2 * Real.pi * Complex.I * d / n) = (d : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have hx1 : x ≠ 1 := by
    rw [hx, Ne, Complex.exp_eq_one_iff]
    rintro ⟨m, hm⟩
    refine hd ⟨m, ?_⟩
    have hdc : (d : ℂ) = (n : ℂ) * m := by
      field_simp at hm
      exact Complex.ext (congrArg Complex.re hm) (congrArg Complex.im hm)
    exact_mod_cast hdc
  rw [geom_sum_eq hx1, hxn, sub_self, zero_div]

/-- Conjugating one Fourier phase and multiplying by another gives the phase of the difference. -/
lemma conj_mul_entry (n : ℕ) (l j k : ℕ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (l * j) / n)) *
        Complex.exp (2 * Real.pi * Complex.I * (l * k) / n)
      = Complex.exp (2 * Real.pi * Complex.I * (l * ((k : ℤ) - j)) / n) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp [Complex.ext_iff]
  ring

/-- The QFT matrix satisfies `QFTᴴ * QFT = 1`. -/
theorem qft_conjTranspose_mul (n : ℕ) (hn : 0 < n) : (qft n)ᴴ * qft n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hsq : (Real.sqrt n : ℂ)⁻¹ * (Real.sqrt n : ℂ)⁻¹ = (n : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_num
  have hstar : star ((Real.sqrt n : ℂ)⁻¹) = (Real.sqrt n : ℂ)⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin n, (qft n)ᴴ j l * qft n l k
      = (n : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) * ((k : ℕ) - (j : ℕ) : ℤ)) / n) := by
    intro l
    simp only [Matrix.conjTranspose_apply, qft, Matrix.of_apply, star_mul', hstar, Complex.star_def]
    rw [show (Real.sqrt n : ℂ)⁻¹ *
          (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) * (j : ℕ)) / n)) *
          ((Real.sqrt n : ℂ)⁻¹ * Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) * (k : ℕ)) / n))
        = ((Real.sqrt n : ℂ)⁻¹ * (Real.sqrt n : ℂ)⁻¹) *
            ((starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) * (j : ℕ)) / n)) *
             Complex.exp (2 * Real.pi * Complex.I * ((l : ℕ) * (k : ℕ)) / n)) from by ring,
      hsq, conj_mul_entry]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun l _ => hterm l), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range
      (fun m => Complex.exp (2 * Real.pi * Complex.I * (m * ((k : ℕ) - (j : ℕ) : ℤ)) / n)) n]
  by_cases hjk : j = k
  · subst hjk
    simp [Matrix.one_apply_eq, Finset.sum_const, hn0]
  · rw [sum_root_pow n hn _ ?_, mul_zero, Matrix.one_apply_ne hjk]
    intro hdvd
    have hz : ((k : ℕ) : ℤ) - (j : ℕ) = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
      have hj := j.isLt
      have hk := k.isLt
      rw [abs_lt]
      omega
    exact hjk (Fin.ext (by omega))

/-- The QFT matrix is unitary. -/
theorem qft_unitary (n : ℕ) (hn : 0 < n) : qft n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  exact mul_eq_one_comm.1 (qft_conjTranspose_mul n hn)

/-- The 6-qubit QFT matrix (dimension `2^6 = 64`) is unitary. -/
theorem qft_unitary_6 : qft 64 ∈ Matrix.unitaryGroup (Fin 64) ℂ :=
  qft_unitary 64 (by norm_num)

end QC

