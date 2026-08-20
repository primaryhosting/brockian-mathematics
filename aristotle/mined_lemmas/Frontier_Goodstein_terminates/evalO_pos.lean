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

lemma evalO_pos {b : ℕ} {x : Ordinal} (hx : 0 < x) {t : HB} (ht : WF b t) (h : t ≠ .zero) :
    0 < evalO x t := by
  cases ht with
  | zero => exact absurd rfl h
  | oadd he hr hc hcb hlt =>
    rename_i e c r
    have h1 : 0 < x ^ evalO x e * (c : Ordinal) :=
      mul_pos (opow_pos _ hx) (by exact_mod_cast hc)
    exact lt_of_lt_of_le h1 le_self_add

