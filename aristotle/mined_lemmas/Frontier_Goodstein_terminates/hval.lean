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


def hval {α : Type*} [Zero α] [Add α] (b : ℕ) (pw : α → α) (mul : α → ℕ → α) (n : ℕ) : α :=
  if _hn : n = 0 then 0
  else
    mul (pw (hval b pw mul (Nat.log b n))) (n / b ^ Nat.log b n)
      + hval b pw mul (n % b ^ Nat.log b n)
termination_by n
decreasing_by
  · exact Nat.log_lt_self b _hn
  · exact mod_pow_log_lt _hn

