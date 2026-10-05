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

The `N`-point quantum Fourier transform matrix
`F_N (j,k) = N^{-1/2} * ω^{j k}` with `ω = exp (2 π i / N)`
is unitary; specialized to `N = 2^6`, the 6-qubit QFT.
-/

namespace QC

open Complex Finset Matrix

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma key_sum {N : ℕ} (hN : N ≠ 0) (j l : Fin N) :
    ∑ k ∈ Finset.range N,
      star (zeta N ^ (k * (j : ℕ))) * zeta N ^ (k * (l : ℕ)) = if j = l then (N : ℂ) else 0 := by
  have hz : IsPrimitiveRoot (zeta N) N := isPrimitiveRoot_zeta hN
  have hzN : zeta N ^ N = 1 := hz.pow_eq_one
  set x : ℂ := (zeta N)⁻¹ ^ (j : ℕ) * zeta N ^ (l : ℕ) with hxdef
  have hterm : ∀ k ∈ Finset.range N,
      star (zeta N ^ (k * (j : ℕ))) * zeta N ^ (k * (l : ℕ)) = x ^ k := by
    intro k _
    rw [hxdef, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) k, mul_comm (l : ℕ) k,
      star_pow, star_zeta]
  rw [Finset.sum_congr rfl hterm]
  by_cases h : j = l
  · have hx1 : x = 1 := by
      rw [hxdef, h, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (zeta_ne_zero N))]
    simp [hx1, h]
  · have hxN : x ^ N = 1 := by
      have hrw : x ^ N = ((zeta N ^ N)⁻¹) ^ (j : ℕ) * (zeta N ^ N) ^ (l : ℕ) := by
        rw [hxdef]; ring
      rw [hrw, hzN]; simp
    have hx1 : x ≠ 1 := by
      intro hc
      rw [hxdef, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ (zeta_ne_zero N))] at hc
      exact h (Fin.val_injective (hz.pow_inj j.isLt l.isLt hc))
    rw [geom_sum_eq hx1, hxN, if_neg h]
    simp

