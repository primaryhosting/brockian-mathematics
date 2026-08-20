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

lemma evalN_pos {b : ℕ} (hb : 1 ≤ b) : ∀ {t : HB}, WF b t → t ≠ .zero → 0 < evalN b t := by
  rintro (_ | ⟨e, c, r⟩) h hne
  · exact absurd rfl hne
  · cases h with
    | oadd he hr hc hcb hlt =>
      have h1 : 0 < b ^ evalN b e * c := Nat.mul_pos (pow_pos hb _) hc
      simp only [evalN]
      omega

