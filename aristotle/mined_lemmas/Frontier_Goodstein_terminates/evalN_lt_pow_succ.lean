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

lemma evalN_lt_pow_succ {b : ℕ} {e : HB} {c : ℕ} {r : HB} (h : WF b (.oadd e c r)) :
    evalN b (.oadd e c r) < b ^ (evalN b e + 1) := by
  cases h with
  | oadd he hr hc hcb hlt =>
    have h1 : b ^ evalN b e * c + b ^ evalN b e ≤ b ^ evalN b e * b := by
      have h2 : b ^ evalN b e * (c + 1) ≤ b ^ evalN b e * b := Nat.mul_le_mul_left _ (by omega)
      simpa [Nat.mul_add] using h2
    simp only [evalN, pow_succ]
    omega

