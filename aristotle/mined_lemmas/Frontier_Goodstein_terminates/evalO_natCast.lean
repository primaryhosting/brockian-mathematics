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

lemma evalO_natCast (b : ℕ) : ∀ t : HB, evalO (b : Ordinal) t = (evalN b t : Ordinal) := by
  intro t
  induction t with
  | zero => simp [evalO, evalN]
  | oadd e c r ihe ihr =>
    rw [evalO, evalN, ihe, ihr, Nat.cast_add, Ordinal.natCast_mul, Ordinal.opow_natCast,
      Ordinal.natCast_pow]

/-- A well-formed base-`b` representation is also a well-formed base-`b'` representation
for any larger base `b'`.  (This is the "base bump" step of Goodstein's process.) -/
