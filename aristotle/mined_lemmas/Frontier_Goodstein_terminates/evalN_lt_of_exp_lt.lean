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

lemma evalN_lt_of_exp_lt {b : ℕ} (hb : 1 ≤ b) {e : HB} {c : ℕ} {r f : HB} {d : ℕ} {s : HB}
    (ht : WF b (.oadd e c r)) (hu : WF b (.oadd f d s)) (h : evalN b e < evalN b f) :
    evalN b (.oadd e c r) < evalN b (.oadd f d s) := by
  have h1 := evalN_lt_pow_succ ht
  have h2 : b ^ (evalN b e + 1) ≤ b ^ evalN b f := Nat.pow_le_pow_right hb (by omega)
  cases hu with
  | oadd hf hs hd hdb hlts =>
    have h3 : b ^ evalN b f ≤ b ^ evalN b f * d := Nat.le_mul_of_pos_right _ hd
    simp only [evalN] at h1 ⊢
    omega

