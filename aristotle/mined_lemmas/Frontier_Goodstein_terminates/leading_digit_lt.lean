import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ### Elementary facts about base-`b` digits -/


lemma leading_digit_lt {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : n / b ^ Nat.log b n < b := by
  rw [Nat.div_lt_iff_lt_mul (pow_log_pos b n)]
  have := Nat.lt_pow_succ_log_self (b := b) (by omega) n
  simpa [pow_succ, Nat.mul_comm] using this

