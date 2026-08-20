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

lemma WF_rep {b : ℕ} (hb : 2 ≤ b) : ∀ n : ℕ, WF b (rep b n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [rep]; exact WF.zero
    | (m + 1) =>
      have hlog : Nat.log b (m + 1) < m + 1 := Nat.log_lt_self b (Nat.succ_ne_zero m)
      have hpos : 0 < b ^ Nat.log b (m + 1) := pow_pos (by omega) _
      have hple : b ^ Nat.log b (m + 1) ≤ m + 1 := Nat.pow_log_le_self b (Nat.succ_ne_zero m)
      have hmod : (m + 1) % b ^ Nat.log b (m + 1) < m + 1 :=
        lt_of_lt_of_le (Nat.mod_lt _ hpos) hple
      rw [rep]
      refine WF.oadd (ih _ hlog) (ih _ hmod) (Nat.div_pos hple hpos) ?_ ?_
      · refine Nat.div_lt_of_lt_mul ?_
        have h1 := Nat.lt_pow_succ_log_self (by omega : 1 < b) (m + 1)
        calc m + 1 < b ^ (Nat.log b (m + 1) + 1) := h1
          _ = b ^ Nat.log b (m + 1) * b := by rw [pow_succ]
          _ = b ^ Nat.log b (m + 1) * b := rfl
      · rw [evalN_rep hb, evalN_rep hb]
        exact Nat.mod_lt _ hpos

end HB

open HB

/-- The Goodstein sequence started at `n`: the `k`-th term lives in base `k + 2`. -/
