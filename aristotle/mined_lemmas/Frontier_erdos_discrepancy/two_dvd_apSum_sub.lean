/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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

namespace Frontier

/-- A `±1` sequence, indexed by the positive naturals (the value at `0` is irrelevant). -/

theorem two_dvd_apSum_sub (hf : IsPlusMinusOne f) {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    (2 : ℤ) ∣ (apSum f d n - (n : ℤ)) := by
  induction n with
  | zero => simp [apSum]
  | succ n ih =>
      rw [apSum_succ]
      have hval : f ((n + 1) * d) = 1 ∨ f ((n + 1) * d) = -1 :=
        hf _ (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.succ_ne_zero n) (by omega)))
      obtain ⟨c, hc⟩ := ih
      rcases hval with h | h <;> rw [h] <;> [exact ⟨c, by push_cast; omega⟩;
        exact ⟨c - 1, by push_cast; omega⟩]

/-- If the discrepancy is at most `1`, every even-length homogeneous AP sum vanishes. -/
