/-
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary 5
Category: Quantum Computing
Target: QC.qft_unitary_5
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

open Complex Matrix

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma conj_qftOmega_pow (n : ℕ) (hn : n ≠ 0) (a : ℕ) (b : ℕ) (hb : b ≤ n) :
    (starRingEnd ℂ) (qftOmega n ^ (a * b)) = qftOmega n ^ (a * (n - b)) := by
  have hconj : (starRingEnd ℂ) (qftOmega n) = (qftOmega n)⁻¹ := by
    unfold qftOmega
    rw [← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      Complex.conj_natCast]
    ring
  have hne : qftOmega n ≠ 0 := by
    unfold qftOmega; exact Complex.exp_ne_zero _
  rw [map_pow, hconj, inv_pow, eq_comm]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add]
  have : a * (n - b) + a * b = n * a := by
    have : n - b + b = n := Nat.sub_add_cancel hb
    calc a * (n - b) + a * b = a * (n - b + b) := by ring
      _ = a * n := by rw [this]
      _ = n * a := Nat.mul_comm _ _
  rw [this, pow_mul, qftOmega_pow_n n hn, one_pow]

