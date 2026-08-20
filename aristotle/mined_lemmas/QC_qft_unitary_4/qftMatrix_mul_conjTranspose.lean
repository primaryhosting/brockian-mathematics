/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The quantum Fourier transform is unitary

We define the `n`-point discrete/quantum Fourier transform matrix

`qftMatrix n = (1/√n) * (ω^(j*k))_{j,k}` with `ω = exp (2πi/n)`,

prove it is unitary for every `n ≠ 0`, and specialize to the 4-qubit case `n = 2^4 = 16`,
giving the target theorem `QC.qft_unitary_4`.
-/

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma qftMatrix_mul_conjTranspose (n : ℕ) [NeZero n] :
    qftMatrix n * (qftMatrix n)ᴴ = 1 := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnorm : ((1 / Real.sqrt n : ℝ) : ℂ) * ((1 / Real.sqrt n : ℝ) : ℂ)
      = ((1 / n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [Real.sqrt_ne_zero'.mpr hnpos]
    exact (Real.sq_sqrt hnpos.le).symm
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n, qftMatrix n j k * (qftMatrix n)ᴴ k l
      = ((1 / n : ℝ) : ℂ) * (zeta n ^ ((j : ℤ) - (l : ℤ))) ^ (k : ℕ) := by
    intro k
    simp only [qftMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_pow,
      star_zeta, Complex.star_def, Complex.conj_ofReal]
    rw [← zeta_pow_sub n j.val l.val k.val, ← hnorm]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun k => (zeta n ^ ((j : ℤ) - (l : ℤ))) ^ k) n]
  by_cases h : j = l
  · subst h
    rw [if_pos rfl]
    simp only [sub_self, zpow_zero, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, one_div,
      inv_mul_cancel₀ (ne_of_gt hnpos), Complex.ofReal_one]
  · rw [if_neg h, zeta_geom_sum, mul_zero]
    have hj := j.isLt
    have hl := l.isLt
    have hne : (j : ℕ) ≠ (l : ℕ) := fun hc => h (Fin.ext hc)
    intro hdvd
    have := Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; omega)
    omega

/-- **The `n`-point quantum Fourier transform matrix is unitary** (for `n ≠ 0`). -/
