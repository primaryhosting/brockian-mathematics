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


lemma leading_digit_pos (b : ℕ) {n : ℕ} (hn : n ≠ 0) : 0 < n / b ^ Nat.log b n :=
  Nat.div_pos (Nat.pow_log_le_self b hn) (pow_log_pos b n)

