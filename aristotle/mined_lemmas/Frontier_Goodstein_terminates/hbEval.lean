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


noncomputable def hbEval (b : ℕ) : ℕ → Ordinal.{0}
  | n =>
    if hn : n = 0 then 0
    else
      Ordinal.omega0 ^ (hbEval b (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) +
        hbEval b (n % b ^ Nat.log b n)
  decreasing_by
  · exact Nat.log_lt_self b hn
  · exact mod_pow_log_lt_self b hn

/-- `baseChange b c n` rewrites `n` in hereditary base `b` and then replaces every
occurrence of the base `b` by `c`. -/
