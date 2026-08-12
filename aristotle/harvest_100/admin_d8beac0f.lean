/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
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

set_option grind.warning false

namespace QC

/-- The primitive `n`-th root of unity `exp (2πi / n)` used to build the QFT matrix. -/
noncomputable def qftRoot (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The `n`-dimensional quantum Fourier transform matrix:
`(QFT n) j k = exp (2πi·j·k/n) / √n`. -/
noncomputable def qftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => qftRoot n ^ ((j : ℕ) * (k : ℕ)) / (Real.sqrt n : ℂ)

/-- Orthogonality relation for the powers of `exp (2πi/n)`. -/
lemma qft_geom_sum (n : ℕ) (hn : n ≠ 0) (j l : Fin n) :
    ∑ k : Fin n, (qftRoot n ^ (j : ℕ) * (qftRoot n)⁻¹ ^ (l : ℕ)) ^ (k : ℕ)
      = if j = l then (n : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (qftRoot n) n := Complex.isPrimitiveRoot_exp n hn
  have hz0 : qftRoot n ≠ 0 := Complex.exp_ne_zero _
  set w : ℂ := qftRoot n ^ (j : ℕ) * (qftRoot n)⁻¹ ^ (l : ℕ) with hw
  have hwn : w ^ n = 1 := by
    rw [hw, mul_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) n, mul_comm (j : ℕ) n, pow_mul,
      inv_pow, pow_mul, hprim.pow_eq_one]
    simp
  rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k)]
  by_cases h : j = l
  · subst h
    have hw1 : w = 1 := by rw [hw, ← mul_pow, mul_inv_cancel₀ hz0, one_pow]
    simp [hw1]
  · have hw1 : w ≠ 1 := by
      intro hcon
      apply h
      rw [hw, inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hz0)] at hcon
      exact Fin.ext (hprim.pow_inj j.isLt l.isLt hcon)
    rw [geom_sum_eq hw1, hwn, sub_self, zero_div, if_neg h]

/-- Complex conjugation inverts `exp (2πi/n)`. -/
lemma conj_qftRoot (n : ℕ) : (starRingEnd ℂ) (qftRoot n) = (qftRoot n)⁻¹ := by
  rw [qftRoot, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [Complex.ext_iff]
  ring

/-- The `n`-dimensional QFT matrix is unitary (for `n ≠ 0`). -/
theorem qftMatrix_mem_unitaryGroup (n : ℕ) (hn : n ≠ 0) :
    qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  have hsq : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hnpos.le, Complex.ofReal_natCast]
  rw [Matrix.mem_unitaryGroup_iff]
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n,
      qftMatrix n j k * (star (qftMatrix n)) k l
        = (qftRoot n ^ (j : ℕ) * (qftRoot n)⁻¹ ^ (l : ℕ)) ^ (k : ℕ) / (n : ℂ) := by
    intro k
    simp only [qftMatrix, Matrix.of_apply, Matrix.star_apply, Complex.star_def, map_div₀,
      map_pow, conj_qftRoot, Complex.conj_ofReal]
    rw [div_mul_div_comm, hsq, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) (k : ℕ),
      mul_comm (l : ℕ) (k : ℕ), pow_mul, pow_mul]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_div, qft_geom_sum n hn j l]
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases h : j = l
  · simp [h, hnC]
  · simp [h]

/-- The 6-qubit quantum Fourier transform matrix (of size `2^6 = 64`) is unitary. -/
theorem qft_unitary_6 : qftMatrix (2 ^ 6) ∈ Matrix.unitaryGroup (Fin (2 ^ 6)) ℂ :=
  qftMatrix_mem_unitaryGroup (2 ^ 6) (by norm_num)

end QC

