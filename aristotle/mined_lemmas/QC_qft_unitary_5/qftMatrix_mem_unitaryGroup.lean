/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `N`-th root of unity `exp (2πi / N)` used in the QFT. -/

theorem qftMatrix_mem_unitaryGroup {N : ℕ} (hN : N ≠ 0) :
    qftMatrix N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  rw [Matrix.mul_apply]
  have hc : star ((Real.sqrt N : ℂ)⁻¹) = (Real.sqrt N : ℂ)⁻¹ := by
    rw [star_inv₀]
    simp
  have hsq : ((Real.sqrt N : ℂ)⁻¹) * ((Real.sqrt N : ℂ)⁻¹) = ((N : ℂ))⁻¹ := by
    rw [← mul_inv]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg N), Complex.ofReal_natCast]
  have key : ∀ k : Fin N, (star (qftMatrix N)) j k * qftMatrix N k l
      = ((N : ℂ))⁻¹ * ((qftRoot N) ^ (l.val) * ((qftRoot N) ^ (j.val))⁻¹) ^ (k.val) := by
    intro k
    rw [Matrix.star_apply]
    simp only [qftMatrix]
    rw [star_mul', hc, star_pow, Complex.star_def, conj_qftRoot]
    rw [← hsq]
    rw [show (Real.sqrt N : ℂ)⁻¹ * (qftRoot N)⁻¹ ^ (k.val * j.val) *
        ((Real.sqrt N : ℂ)⁻¹ * qftRoot N ^ (k.val * l.val))
        = ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹) *
          ((qftRoot N)⁻¹ ^ (k.val * j.val) * qftRoot N ^ (k.val * l.val)) from by ring]
    rw [inv_pow_mul_pow]
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, qft_geom_sum hN j l]
  by_cases h : j = l
  · subst h
    rw [if_pos rfl, inv_mul_cancel₀ (by exact_mod_cast hN), Matrix.one_apply_eq]
  · rw [if_neg h, mul_zero, Matrix.one_apply_ne h]

/-- **The 5-qubit quantum Fourier transform matrix is unitary.** -/
