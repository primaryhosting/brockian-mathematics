/-
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 8
Category: Quantum Computing
Target: QC.qft_unitary_8
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

/-- The `N × N` discrete (quantum) Fourier transform matrix: its `(j, k)` entry is
`N^(-1/2) * exp (2 π i j k / N)`. -/

theorem sum_zeta_orthogonality (hN : N ≠ 0) (a b : Fin N) :
    (∑ j : Fin N, ((zetaN N)⁻¹ ^ a.val * zetaN N ^ b.val) ^ j.val) =
      if a = b then (N : ℂ) else 0 := by
  set w : ℂ := (zetaN N)⁻¹ ^ a.val * zetaN N ^ b.val with hw
  have hzeta := isPrimitiveRoot_zetaN (N := N) hN
  have hpowN : zetaN N ^ N = 1 := hzeta.pow_eq_one
  have hwN : w ^ N = 1 := by
    rw [hw, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val N, mul_comm b.val N, pow_mul, pow_mul,
      hpowN, inv_pow, hpowN]
    simp
  have hinv : ∀ m : ℕ, (zetaN N)⁻¹ ^ m * zetaN N ^ m = 1 := by
    intro m
    rw [← mul_pow, inv_mul_cancel₀ (zetaN_ne_zero (N := N)), one_pow]
  by_cases hab : a = b
  · subst hab
    have hw1 : w = 1 := hinv a.val
    simp [hw1]
  · have hwne : w ≠ 1 := by
      intro h
      apply hab
      have h2 : zetaN N ^ b.val = zetaN N ^ a.val := by
        calc zetaN N ^ b.val = (zetaN N)⁻¹ ^ a.val * zetaN N ^ b.val * zetaN N ^ a.val := by
              rw [mul_comm ((zetaN N)⁻¹ ^ a.val) (zetaN N ^ b.val), mul_assoc, hinv a.val, mul_one]
          _ = 1 * zetaN N ^ a.val := by rw [← hw, h]
          _ = zetaN N ^ a.val := one_mul _
      exact (Fin.ext (hzeta.pow_inj b.isLt a.isLt h2)).symm
    have hrange : (∑ j : Fin N, w ^ j.val) = ∑ i ∈ Finset.range N, w ^ i := by
      rw [Finset.sum_range fun i => w ^ i]
    rw [hrange, geom_sum_eq hwne, hwN]
    simp [hab]

/-- The `N × N` QFT matrix is unitary for every `N ≠ 0`. -/
