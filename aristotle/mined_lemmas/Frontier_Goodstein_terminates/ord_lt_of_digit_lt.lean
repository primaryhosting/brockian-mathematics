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

lemma ord_lt_of_digit_lt {x A er es : Ordinal} {c d : ℕ} (hcd : c < d) (her : er < x ^ A) :
    x ^ A * (c : Ordinal) + er < x ^ A * (d : Ordinal) + es := by
  have h1 : x ^ A * (c : Ordinal) + er < x ^ A * (c : Ordinal) + x ^ A :=
    add_lt_add_right her _
  have h2 : x ^ A * (c : Ordinal) + x ^ A = x ^ A * ((c : Ordinal) + 1) := by
    rw [mul_add, mul_one]
  have h3 : x ^ A * ((c : Ordinal) + 1) ≤ x ^ A * (d : Ordinal) := by
    refine mul_le_mul_right ?_ _
    exact_mod_cast Nat.succ_le_of_lt hcd
  exact lt_of_lt_of_le (h1.trans_eq h2) (h3.trans le_self_add)

/-- The master comparison lemma: for well-formed base-`b` trees, the numerical order in base `b`
is reflected by the ordinal order after replacing the base by any ordinal `x ≥ b`. -/
