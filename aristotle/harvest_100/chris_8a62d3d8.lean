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
noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- The `N`-point quantum Fourier transform matrix. -/
noncomputable def qftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun j k => ((Real.sqrt N : ℝ) : ℂ)⁻¹ * zeta N ^ ((j : ℕ) * (k : ℕ))

lemma isPrimitiveRoot_zeta {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N := by
  have h := Complex.isPrimitiveRoot_exp N hN
  convert h using 2

lemma star_zeta (N : ℕ) : star (zeta N) = (zeta N)⁻¹ := by
  show (starRingEnd ℂ) _ = _
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_I, map_ofNat]
  ring

lemma zeta_ne_zero (N : ℕ) : zeta N ≠ 0 := Complex.exp_ne_zero _

/-- Orthogonality of the columns of the (unnormalized) Fourier matrix. -/
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

lemma inv_sqrt_sq {N : ℕ} :
    ((Real.sqrt N : ℝ) : ℂ)⁻¹ * ((Real.sqrt N : ℝ) : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  norm_cast

theorem qft_conjTranspose_mul {N : ℕ} (hN : N ≠ 0) :
    (qftMatrix N)ᴴ * qftMatrix N = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin N, (qftMatrix N)ᴴ j k * qftMatrix N k l
      = (N : ℂ)⁻¹ * (star (zeta N ^ ((k : ℕ) * (j : ℕ))) * zeta N ^ ((k : ℕ) * (l : ℕ))) := by
    intro k
    simp only [Matrix.conjTranspose_apply, qftMatrix, Matrix.of_apply, star_mul',
      Complex.star_def, Complex.conj_ofReal, map_inv₀]
    rw [← inv_sqrt_sq]
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  have : ∑ k : Fin N, (star (zeta N ^ ((k : ℕ) * (j : ℕ))) * zeta N ^ ((k : ℕ) * (l : ℕ)))
      = ∑ k ∈ Finset.range N, (star (zeta N ^ (k * (j : ℕ))) * zeta N ^ (k * (l : ℕ))) :=
    Fin.sum_univ_eq_sum_range
      (fun k => star (zeta N ^ (k * (j : ℕ))) * zeta N ^ (k * (l : ℕ))) N
  rw [this, key_sum hN j l, Matrix.one_apply]
  by_cases h : j = l
  · simp [h, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN : (N : ℂ) ≠ 0)]
  · simp [h]

theorem qft_mul_conjTranspose {N : ℕ} (hN : N ≠ 0) :
    qftMatrix N * (qftMatrix N)ᴴ = 1 :=
  mul_eq_one_comm.mp (qft_conjTranspose_mul hN)

/-- The 6-qubit quantum Fourier transform matrix is unitary. -/
theorem qft_unitary_6 : qftMatrix (2 ^ 6) ∈ Matrix.unitaryGroup (Fin (2 ^ 6)) ℂ := by
  constructor
  · exact qft_conjTranspose_mul (by norm_num)
  · exact qft_mul_conjTranspose (by norm_num)

end QC

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

