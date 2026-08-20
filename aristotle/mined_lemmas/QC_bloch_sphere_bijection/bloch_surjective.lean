import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
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

/-- A pure qubit state: a unit vector in `ℂ²`. -/

theorem bloch_surjective : Function.Surjective bloch := by
  rintro ⟨p, hp⟩
  by_cases hz : p 2 = -1
  · refine ⟨Quotient.mk qubitSetoid ⟨![0, 1], by norm_num⟩, ?_⟩
    rw [bloch_mk]
    apply Sphere2.ext
    intro i
    have hxy : p 0 ^ 2 + p 1 ^ 2 = 0 := by rw [hz] at hp; nlinarith
    have hx : p 0 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have hy : p 1 = 0 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    fin_cases i <;> simp [blochRaw, hx, hy, hz]
  · -- p 2 ≠ -1, so 1 + p 2 > 0
    have hple : p 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (p 0), sq_nonneg (p 1)]
    have hge : -1 ≤ p 2 := by nlinarith
    have hpos : 0 < 1 + p 2 := by
      rcases lt_or_eq_of_le hge with h | h
      · linarith
      · exact absurd h.symm hz
    set a : ℝ := Real.sqrt ((1 + p 2) / 2) with ha
    have ha2 : a ^ 2 = (1 + p 2) / 2 := Real.sq_sqrt (by positivity)
    have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
    refine ⟨Quotient.mk qubitSetoid ⟨![(a : ℂ), (p 0 / (2 * a) : ℝ) + (p 1 / (2 * a) : ℝ) * Complex.I], ?_⟩, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp
      nlinarith [hp, ha2, hapos]
    · rw [bloch_mk]
      apply Sphere2.ext
      intro i
      have hane : (a : ℝ) ≠ 0 := ne_of_gt hapos
      have hprod : (starRingEnd ℂ) ((a : ℝ) : ℂ) *
          ((((p 0 / (2 * a) : ℝ)) : ℂ) + (((p 1 / (2 * a) : ℝ)) : ℂ) * Complex.I) =
          (((p 0 / 2 : ℝ)) : ℂ) + (((p 1 / 2 : ℝ)) : ℂ) * Complex.I := by
        have hanec : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hane
        rw [Complex.conj_ofReal]
        push_cast
        field_simp
      have hnb : ‖(((p 0 / (2 * a) : ℝ)) : ℂ) + (((p 1 / (2 * a) : ℝ)) : ℂ) * Complex.I‖ ^ 2
          = (1 - p 2) / 2 := by
        rw [Complex.sq_norm]
        simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        field_simp
        nlinarith [hp, ha2, hapos]
      have hna : ‖((a : ℝ) : ℂ)‖ ^ 2 = (1 + p 2) / 2 := by
        rw [Complex.sq_norm]
        simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
        nlinarith [ha2]
      fin_cases i <;>
        simp only [blochRaw, Matrix.cons_val_zero, Matrix.cons_val_one,
          Fin.zero_eta, Fin.mk_one, Fin.isValue,
          hprod, hnb, hna, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      · ring
      · ring
      · show (1 + p 2) / 2 - (1 - p 2) / 2 = p 2
        ring

/-- **Bloch sphere bijection**: pure qubit states modulo global phase are in bijection with
the points of the 2-sphere `S²`. -/
