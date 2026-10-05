/-
# Qft Unitary 3
Category: Quantum Computing
Target: QC.qft_unitary_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

/-- The primitive 8-th root of unity used by the 3-qubit QFT. -/

lemma conj_zeta8 : (starRingEnd ℂ) zeta8 = zeta8 ^ 7 := by
  have h1 : zeta8 * (starRingEnd ℂ) zeta8 = 1 := by
    rw [zeta8, ← Complex.exp_conj, ← Complex.exp_add]
    have hz0 : (2 * (Real.pi : ℂ) * Complex.I / 8) +
        (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I / 8) = 0 := by
      simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring
    rw [hz0, Complex.exp_zero]
  have h2 : zeta8 * zeta8 ^ 7 = 1 := by
    calc zeta8 * zeta8 ^ 7 = zeta8 ^ 8 := by ring
      _ = 1 := zeta8_pow_eight
  have hz : zeta8 ≠ 0 := by
    intro hc
    rw [hc] at h2
    simp at h2
  exact mul_left_cancel₀ hz (h1.trans h2.symm)

/-- The 3-qubit QFT matrix is unitary. -/
