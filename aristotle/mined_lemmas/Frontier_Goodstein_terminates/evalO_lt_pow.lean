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

lemma evalO_lt_pow {b : ℕ} (hb : 2 ≤ b) {x : Ordinal} (hx : (b : Ordinal) ≤ x) {t E : HB}
    (ht : WF b t) (hE : WF b E) (h : evalN b t < b ^ evalN b E) : evalO x t < x ^ evalO x E :=
  (key hb hx (t.size + E.size)).2 t E le_rfl ht hE h

/-- Evaluating at a natural ordinal base agrees with the numerical evaluation. -/
