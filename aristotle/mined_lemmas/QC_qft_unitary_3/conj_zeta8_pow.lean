import Mathlib

/-!
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
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

/-- The primitive 8-th root of unity `exp (2 π i / 8)`. -/

lemma conj_zeta8_pow (a : ℕ) :
    (starRingEnd ℂ) (zeta8 ^ a) = zeta8 ^ (7 * a) := by
  have hconj : (starRingEnd ℂ) zeta8 = zeta8⁻¹ := by
    have h1 : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 8)
        = -(2 * (Real.pi : ℂ) * Complex.I / 8) := by
      simp [map_div₀, Complex.conj_I]
      ring
    calc (starRingEnd ℂ) zeta8
        = Complex.exp ((starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 8)) := by
          rw [zeta8, Complex.exp_conj]
      _ = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I / 8)) := by rw [h1]
      _ = zeta8⁻¹ := by rw [Complex.exp_neg, zeta8]
  have hmul : zeta8 ^ a * zeta8 ^ (7 * a) = 1 := by
    rw [← pow_add]
    have h : a + 7 * a = 8 * a := by ring
    rw [h, pow_mul, zeta8_pow_eight, one_pow]
  rw [map_pow, hconj, inv_pow]
  exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm] at hmul; exact hmul)).symm

/-- Geometric sums of nontrivial powers of `zeta8` vanish. -/
