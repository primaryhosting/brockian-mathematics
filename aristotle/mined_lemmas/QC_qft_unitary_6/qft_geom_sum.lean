/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QC

/-- The primitive `n`-th root of unity `exp (2πi / n)` used to build the QFT matrix. -/

lemma qft_geom_sum (n : ℕ) (hn : n ≠ 0) (j l : Fin n) :
    ∑ k : Fin n, (qftRoot n ^ (j : ℕ) * (qftRoot n)⁻¹ ^ (l : ℕ)) ^ (k : ℕ)
      = if j = l then (n : ℂ) else 0 := by
  have hprim : IsPrimitiveRoot (qftRoot n) n := Complex.isPrimitiveRoot_exp n hn
  have hz0 : qftRoot n ≠ 0 := Complex.exp_ne_zero _
  set w : ℂ := qftRoot n ^ (j : ℕ) * (qftRoot n)⁻¹ ^ (l : ℕ) with hw
  have hwn : w ^ n = 1 := by
    rw [hw, mul_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) n, mul_comm (j : ℕ) n, pow_mul,
      inv_pow, pow_mul, hprim.pow_eq_one]
    simp
  rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k)]
  by_cases h : j = l
  · subst h
    have hw1 : w = 1 := by rw [hw, ← mul_pow, mul_inv_cancel₀ hz0, one_pow]
    simp [hw1]
  · have hw1 : w ≠ 1 := by
      intro hcon
      apply h
      rw [hw, inv_pow, ← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hz0)] at hcon
      exact Fin.ext (hprim.pow_inj j.isLt l.isLt hcon)
    rw [geom_sum_eq hw1, hwn, sub_self, zero_div, if_neg h]

/-- Complex conjugation inverts `exp (2πi/n)`. -/
