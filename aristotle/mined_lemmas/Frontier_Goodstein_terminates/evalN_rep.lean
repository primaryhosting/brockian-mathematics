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

lemma evalN_rep {b : ℕ} (hb : 2 ≤ b) : ∀ n : ℕ, evalN b (rep b n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [rep, evalN]
    | (m + 1) =>
      have hlog : Nat.log b (m + 1) < m + 1 := Nat.log_lt_self b (Nat.succ_ne_zero m)
      have hpos : 0 < b ^ Nat.log b (m + 1) := pow_pos (by omega) _
      have hmod : (m + 1) % b ^ Nat.log b (m + 1) < m + 1 :=
        lt_of_lt_of_le (Nat.mod_lt _ hpos) (Nat.pow_log_le_self b (Nat.succ_ne_zero m))
      rw [rep, evalN, ih _ hlog, ih _ hmod]
      exact Nat.div_add_mod (m + 1) _

