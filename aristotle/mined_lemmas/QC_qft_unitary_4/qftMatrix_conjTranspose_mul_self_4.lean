import Mathlib
/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Complex Finset Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)` used by the quantum Fourier transform. -/

lemma qftMatrix_conjTranspose_mul_self_4 :
    (qftMatrix 16)ᴴ * (qftMatrix 16) = 1 := by
  have hprim : IsPrimitiveRoot (qftOmega 16) 16 := qftOmega_isPrimitiveRoot 16 (by norm_num)
  have hsqrt : ((Real.sqrt (16 : ℕ) : ℝ) : ℂ) = 4 := by
    push_cast
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have hne : qftOmega 16 ≠ 0 := qftOmega_ne_zero 16
  set w := qftOmega 16 with hw
  ext j l
  rw [Matrix.mul_apply]
  -- Each summand is the `k`-th power of `z = ω^l * (ω^j)⁻¹`, divided by `16`.
  have key : ∀ k : Fin 16, (qftMatrix 16)ᴴ j k * qftMatrix 16 k l
      = ((w ^ (l : ℕ) * (w ^ (j : ℕ))⁻¹) ^ (k : ℕ)) / 16 := by
    intro k
    rw [Matrix.conjTranspose_apply]
    simp only [qftMatrix, hsqrt, ← hw]
    rw [show star (w ^ ((k : ℕ) * (j : ℕ)) / 4) = (w⁻¹) ^ ((k : ℕ) * (j : ℕ)) / 4 from by
      simp [hw, star_qftOmega]]
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, div_mul_div_comm]
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun k => (w ^ (l : ℕ) * (w ^ (j : ℕ))⁻¹) ^ k) 16]
  by_cases hjl : j = l
  · -- Diagonal entries: the geometric sum has all terms equal to `1`.
    subst hjl
    rw [mul_inv_cancel₀ (pow_ne_zero _ hne)]
    simp [Matrix.one_apply_eq]
  · -- Off-diagonal: `z ≠ 1` is a 16-th root of unity, so the geometric sum vanishes.
    have hz1 : w ^ (l : ℕ) * (w ^ (j : ℕ))⁻¹ ≠ 1 := by
      intro h
      apply hjl
      have h2 : w ^ (l : ℕ) = w ^ (j : ℕ) := by
        field_simp at h
        exact h
      exact (Fin.ext (hprim.pow_inj l.isLt j.isLt h2)).symm
    have hzn : (w ^ (l : ℕ) * (w ^ (j : ℕ))⁻¹) ^ 16 = 1 := by
      rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) 16, mul_comm (j : ℕ) 16,
        pow_mul, pow_mul]
      simp [hprim.pow_eq_one]
    rw [geom_sum_eq hz1, hzn]
    simp [Matrix.one_apply_ne hjl]

/-- The 4-qubit quantum Fourier transform matrix is unitary. -/
