/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-! ## Elementary facts about base-`b` digits -/


theorem digit_pos {b n : ℕ} (hn : n ≠ 0) : 1 ≤ n / b ^ Nat.log b n :=
  (Nat.one_le_div_iff (pow_log_pos b n)).2 (Nat.pow_log_le_self b hn)

