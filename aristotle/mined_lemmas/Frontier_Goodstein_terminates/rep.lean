/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring command, so the header above is
-- kept verbatim as a plain block comment.)

import Mathlib

namespace Frontier

open Ordinal

/-- Syntax trees for hereditary base-`b` representations:
`oadd e c r` denotes `b ^ (value of e) * c + (value of r)`. -/
inductive HB where
  | zero : HB
  | oadd : HB → ℕ → HB → HB
deriving DecidableEq

namespace HB

/-- Size of a tree, used as a termination measure. -/

def rep (b : ℕ) : ℕ → HB
  | 0 => .zero
  | (n + 1) =>
      .oadd (rep b (Nat.log b (n + 1))) ((n + 1) / b ^ Nat.log b (n + 1))
        (rep b ((n + 1) % b ^ Nat.log b (n + 1)))
  decreasing_by
  · exact Nat.log_lt_self b (Nat.succ_ne_zero n)
  · have hpos : 0 < b ^ Nat.log b (n + 1) := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · subst hb; rw [Nat.log_zero_left]; norm_num
      · positivity
    exact lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.pow_log_le_self b (Nat.succ_ne_zero n))

/-! ### Numerical lemmas -/

