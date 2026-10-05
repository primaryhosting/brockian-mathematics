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

lemma eq_of_dvd_lt_two_mul {n s : ℕ} (h0 : 0 < s) (h2 : s < 2 * n) (hd : n ∣ s) : s = n := by
  obtain ⟨t, rfl⟩ := hd
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at h0
    · exact h
  have ht2 : t < 2 := by
    by_contra hc
    push_neg at hc
    have : 2 * n ≤ n * t := by nlinarith
    omega
  have ht0 : t ≠ 0 := by rintro rfl; simp at h0
  have : t = 1 := by omega
  subst this
  simp

/-- The `n`-point QFT matrix is unitary. -/
