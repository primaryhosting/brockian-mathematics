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

/-- The primitive 16-th root of unity `exp (2πi/16)`. -/

lemma conj_zeta16 : (starRingEnd ℂ) zeta16 = zeta16 ^ (15 : ℕ) := by
  have c2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_eq_iff_re.mpr rfl
  have c16 : (starRingEnd ℂ) (16 : ℂ) = 16 := Complex.conj_eq_iff_re.mpr rfl
  have hc : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 16)
      = -(2 * (Real.pi : ℂ) * Complex.I / 16) := by
    rw [map_div₀, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, c2, c16]
    ring
  have h1 : (starRingEnd ℂ) zeta16 = Complex.exp (-(2 * Real.pi * Complex.I / 16)) := by
    rw [zeta16, ← Complex.exp_conj, hc]
  have h2 : zeta16 * (starRingEnd ℂ) zeta16 = 1 := by
    rw [h1, zeta16, ← Complex.exp_add]
    simp
  have h3 : zeta16 * zeta16 ^ (15 : ℕ) = 1 := by
    rw [← pow_succ']
    exact zeta16_pow_16
  have := h2.trans h3.symm
  exact mul_left_cancel₀ zeta16_ne_zero this

/-- The 4-qubit quantum Fourier transform matrix, of size `16 × 16`. -/
