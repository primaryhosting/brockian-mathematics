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


lemma mod_pow_log_lt_self (b : ℕ) {n : ℕ} (hn : n ≠ 0) : n % b ^ Nat.log b n < n :=
  lt_of_lt_of_le (Nat.mod_lt _ (pow_log_pos b n)) (Nat.pow_log_le_self b hn)

