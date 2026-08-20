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

noncomputable def evalO (x : Ordinal) : HB → Ordinal
  | .zero => 0
  | .oadd e c r => x ^ (evalO x e) * (c : Ordinal) + evalO x r

/-- Well-formedness of a hereditary base-`b` representation: digits are nonzero and `< b`,
exponents are again well formed, and the tail is smaller than `b ^ (leading exponent)`
(which encodes that exponents are strictly decreasing). -/
inductive WF (b : ℕ) : HB → Prop
  | zero : WF b .zero
  | oadd {e c r} : WF b e → WF b r → 0 < c → c < b →
      evalN b r < b ^ evalN b e → WF b (.oadd e c r)

/-- The canonical hereditary base-`b` representation of a natural number. -/
