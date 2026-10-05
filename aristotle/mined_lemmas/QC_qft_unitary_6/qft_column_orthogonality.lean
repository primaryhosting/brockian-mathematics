/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

open Complex Matrix Finset

/-- The primitive `64`-th root of unity `exp (2πi/64)` used by the 6-qubit QFT. -/

theorem qft_column_orthogonality (a b : Fin 64) :
    ∑ m : Fin 64, (qftOmega⁻¹) ^ (m.val * a.val) * qftOmega ^ (m.val * b.val)
      = if a = b then (64 : ℂ) else 0 := by
  set x : ℂ := (qftOmega⁻¹) ^ a.val * qftOmega ^ b.val with hx
  have hterm : ∀ m : Fin 64,
      (qftOmega⁻¹) ^ (m.val * a.val) * qftOmega ^ (m.val * b.val) = x ^ m.val := by
    intro m
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val m.val, mul_comm b.val m.val]
  rw [Finset.sum_congr rfl fun m _ => hterm m, Fin.sum_univ_eq_sum_range (fun m => x ^ m) 64]
  by_cases hab : a = b
  · subst hab
    have : x = 1 := by
      rw [hx, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ qftOmega_ne_zero)]
    simp [this]
  · have hx1 : x ≠ 1 := by
      intro h
      apply hab
      rw [hx, inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ qftOmega_ne_zero)] at h
      exact Fin.ext (isPrimitiveRoot_qftOmega.pow_inj a.isLt b.isLt h)
    have hx64 : x ^ 64 = 1 := by
      rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm a.val 64, mul_comm b.val 64,
        pow_mul, pow_mul, inv_pow, qftOmega_pow_64]
      simp
    rw [geom_sum_eq hx1, hx64, sub_self, zero_div, if_neg hab]

/-- The 6-qubit QFT matrix is unitary. -/
