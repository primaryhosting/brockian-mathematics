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

lemma evalO_lt_of_evalN_lt {b : ℕ} (hb : 2 ≤ b) {x : Ordinal} (hx : (b : Ordinal) ≤ x) {t u : HB}
    (ht : WF b t) (hu : WF b u) (h : evalN b t < evalN b u) : evalO x t < evalO x u :=
  ((key hb hx (t.size + u.size)).1 t u le_rfl ht hu).1 h

