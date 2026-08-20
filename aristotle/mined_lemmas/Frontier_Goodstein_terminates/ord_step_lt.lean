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

lemma ord_step_lt {b : ℕ} (hb : 2 ≤ b) {m : ℕ} (hm : m ≠ 0) :
    ord (b + 1) (evalN (b + 1) (rep b m) - 1) < ord b m := by
  have hb1 : 2 ≤ b + 1 := by omega
  have ht : WF b (rep b m) := WF_rep hb m
  have ht' : WF (b + 1) (rep b m) := WF_mono hb (by omega) ht
  have hval : evalN b (rep b m) = m := evalN_rep hb m
  have hne : rep b m ≠ .zero := by
    intro h
    rw [h] at hval
    exact hm (by simpa [evalN] using hval.symm)
  have hM : 0 < evalN (b + 1) (rep b m) := evalN_pos (by omega) ht' hne
  have h1 : evalN (b + 1) (rep (b + 1) (evalN (b + 1) (rep b m) - 1))
      = evalN (b + 1) (rep b m) - 1 := evalN_rep hb1 _
  have h2 : evalN (b + 1) (rep (b + 1) (evalN (b + 1) (rep b m) - 1))
      < evalN (b + 1) (rep b m) := by omega
  have hx : ((b + 1 : ℕ) : Ordinal.{0}) ≤ Ordinal.omega0.{0} := le_of_lt (Ordinal.nat_lt_omega0 _)
  simpa [ord] using evalO_lt_of_evalN_lt hb1 hx (WF_rep hb1 _) ht' h2

-- Sanity check (evaluation only, not part of the proof):
-- `#eval (List.range 6).map (goodstein 3)` produces `[3, 3, 3, 2, 1, 0]`, and
-- `#eval (List.range 6).map (goodstein 4)` produces `[4, 26, 41, 60, 83, 109]`,
-- the classical Goodstein sequences for 3 and 4.

/-- **Goodstein's theorem**: every Goodstein sequence reaches `0`. -/
