import Mathlib

/-!
# Qft Unitary 7
Category: Quantum Computing
Target: QC.qft_unitary_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset Matrix

/-- The `n × n` quantum Fourier transform matrix, with entries
`exp (2 π i j k / n) / √n`. -/

lemma qft_conjTranspose_mul (n : ℕ) (hn : 0 < n) : (qft n)ᴴ * (qft n) = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsq : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    norm_num
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin n, (qft n)ᴴ j k * qft n k l
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          ((k : ℕ) * ((((l : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ℂ)) / n) / n := by
    intro k
    rw [Matrix.conjTranspose_apply, qft_apply, qft_apply, Complex.star_def, map_div₀,
      ← Complex.exp_conj]
    simp only [Complex.conj_ofReal, map_div₀, map_mul, map_ofNat,
      Complex.conj_I, Complex.conj_natCast]
    rw [div_mul_div_comm, hsq, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hterm k, ← Finset.sum_div,
    sum_exp_eq n hn (((l : ℕ) : ℤ) - ((j : ℕ) : ℤ))]
  by_cases hjl : j = l
  · subst hjl
    simp [hn0]
  · have hne : ¬ ((n : ℤ) ∣ (((l : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
      intro hd
      apply hjl
      have hj := j.isLt
      have hl := l.isLt
      have habs : |(((l : ℕ) : ℤ) - ((j : ℕ) : ℤ))| < (n : ℤ) := by
        rw [abs_lt]
        constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hd habs
      exact Fin.ext (by omega)
    rw [if_neg hne, if_neg hjl, zero_div]

/-- The 7-qubit quantum Fourier transform matrix (of size `2^7 = 128`) is unitary. -/
