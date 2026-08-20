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

lemma ord_term_lt {x α β : Ordinal} {c : ℕ} (hc : (c : Ordinal) < x)
    (hβ : β < x ^ α) : x ^ α * (c : Ordinal) + β < x ^ (α + 1) := by
  have h1 : x ^ α * (c : Ordinal) + β < x ^ α * (c : Ordinal) + x ^ α :=
    add_lt_add_right hβ _
  have h2 : x ^ α * (c : Ordinal) + x ^ α = x ^ α * ((c : Ordinal) + 1) := by
    rw [mul_add, mul_one]
  have h3 : x ^ α * ((c : Ordinal) + 1) ≤ x ^ α * x :=
    mul_le_mul_right (Order.add_one_le_iff.mpr hc) _
  have h4 : x ^ α * x = x ^ (α + 1) := by rw [Ordinal.opow_add, Ordinal.opow_one]
  exact lt_of_lt_of_le (h1.trans_eq h2) (h3.trans_eq h4)

