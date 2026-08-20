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


def baseChange (b c : ℕ) : ℕ → ℕ
  | n =>
    if hn : n = 0 then 0
    else
      c ^ (baseChange b c (Nat.log b n)) * (n / b ^ Nat.log b n) +
        baseChange b c (n % b ^ Nat.log b n)
  decreasing_by
  · exact Nat.log_lt_self b hn
  · exact mod_pow_log_lt_self b hn

