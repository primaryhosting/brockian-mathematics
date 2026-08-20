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

lemma WF_mono {b b' : ℕ} (hb : 2 ≤ b) (hbb : b ≤ b') : ∀ {t : HB}, WF b t → WF b' t := by
  intro t ht
  induction ht with
  | zero => exact WF.zero
  | oadd he hr hc hcb hlt ihe ihr =>
    refine WF.oadd ihe ihr hc (lt_of_lt_of_le hcb hbb) ?_
    have hx : (b : Ordinal.{0}) ≤ (b' : Ordinal.{0}) := by exact_mod_cast hbb
    have h := evalO_lt_pow hb hx hr he hlt
    rw [evalO_natCast, evalO_natCast, Ordinal.opow_natCast, ← Ordinal.natCast_pow] at h
    exact_mod_cast h

/-! ### The canonical representation -/

