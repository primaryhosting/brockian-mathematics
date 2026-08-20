/-
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

namespace Frontier.Spectral

open Complex Finset Matrix

/-! ## Definitions -/

/-- The `n`-th root of unity `exp (2πI/n)`. -/

theorem dftInv_mul_dft {n : ℕ} (hn : n ≠ 0) :
    dftInvMatrix n * dftMatrix n = 1 := by
  have hz0 : zetaN n ≠ 0 := zetaN_ne_zero n
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : Fin n,
      dftInvMatrix n j k * dftMatrix n k l
        = (n : ℂ)⁻¹ * ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    have h1 : ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ (k : ℕ)
        = zetaN n ^ ((k : ℕ) * (l : ℕ)) * (zetaN n ^ ((j : ℕ) * (k : ℕ)))⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) (k : ℕ),
        mul_comm (j : ℕ) (k : ℕ)]
    simp only [dftInvMatrix, dftMatrix, h1]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum]
  have hsum : ∑ k : Fin n, ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ (k : ℕ)
      = ∑ k ∈ Finset.range n, ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ k :=
    Fin.sum_univ_eq_sum_range
      (fun k => ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ k) n
  rw [hsum]
  by_cases hjl : j = l
  · have hx1 : (zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹ = 1 := by
      rw [hjl]
      exact mul_inv_cancel₀ (pow_ne_zero _ hz0)
    rw [hx1, hjl, Matrix.one_apply_eq]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hnC
  · have hjne : zetaN n ^ (j : ℕ) ≠ 0 := pow_ne_zero _ hz0
    have hxne : (zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹ ≠ 1 := by
      intro hx1
      rw [mul_inv_eq_one₀ hjne] at hx1
      exact hjl (Fin.ext ((isPrimitiveRoot_zetaN hn).pow_inj l.isLt j.isLt hx1)).symm
    have hxn : ((zetaN n ^ (l : ℕ)) * (zetaN n ^ (j : ℕ))⁻¹) ^ n = 1 := by
      have h1 : (zetaN n ^ (l : ℕ)) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, zetaN_pow_n hn, one_pow]
      have h2 : (zetaN n ^ (j : ℕ)) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, zetaN_pow_n hn, one_pow]
      rw [mul_pow, inv_pow, h1, h2, inv_one, mul_one]
    rw [geom_sum_eq hxne, hxn, Matrix.one_apply_ne hjl]
    simp

/-- The DFT matrix is invertible. -/
