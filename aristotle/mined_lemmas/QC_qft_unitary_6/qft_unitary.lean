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

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

theorem qft_unitary (n : ℕ) (hn : n ≠ 0) : qftMatrix n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, qftMatrix_apply, Matrix.one_apply]
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : ((1 / Real.sqrt n : ℝ) : ℂ) * ((1 / Real.sqrt n : ℝ) : ℂ) = ((n : ℂ))⁻¹ := by
    rw [← Complex.ofReal_mul]
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt hnR]
    push_cast
    ring
  have hstep : ∀ x : Fin n,
      ((1 / Real.sqrt n : ℝ) : ℂ) * zeta n ^ ((k : ℕ) * (x : ℕ)) *
          star (((1 / Real.sqrt n : ℝ) : ℂ) * zeta n ^ ((l : ℕ) * (x : ℕ)))
        = (((1 / Real.sqrt n : ℝ) : ℂ) * ((1 / Real.sqrt n : ℝ) : ℂ)) *
            (zeta n ^ ((k : ℕ) * (x : ℕ)) * (zeta n ^ ((l : ℕ) * (x : ℕ)))⁻¹) := by
    intro x
    rw [star_mul']
    rw [show star (((1 / Real.sqrt n : ℝ) : ℂ)) = ((1 / Real.sqrt n : ℝ) : ℂ) from
      Complex.conj_ofReal _]
    rw [show star (zeta n ^ ((l : ℕ) * (x : ℕ))) = (zeta n ^ ((l : ℕ) * (x : ℕ)))⁻¹ from
      conj_zeta_pow n _]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hstep x), ← Finset.mul_sum, hc,
    qft_row_orthogonality n hn k l]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases hkl : k = l
  · simp [hkl, inv_mul_cancel₀ hn']
  · simp [hkl]

/-- The 6-qubit QFT matrix (of size `2^6 = 64`) is unitary. -/
