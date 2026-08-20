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

lemma nat_digit_lt {P c r d s : ℕ} (hs : s < P) (h : P * c + r < P * d + s) :
    c < d ∨ (c = d ∧ r < s) := by
  rcases lt_trichotomy c d with h1 | h1 | h1
  · exact Or.inl h1
  · subst h1; exact Or.inr ⟨rfl, by omega⟩
  · exfalso
    have h2 : P * (d + 1) ≤ P * c := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega

