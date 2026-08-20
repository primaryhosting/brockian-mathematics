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


lemma mod_lt_pow_log (b n : ℕ) : n % b ^ Nat.log b n < b ^ Nat.log b n :=
  Nat.mod_lt _ (pow_log_pos b n)

