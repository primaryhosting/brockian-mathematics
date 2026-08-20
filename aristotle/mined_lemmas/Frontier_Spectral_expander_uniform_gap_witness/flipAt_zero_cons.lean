/-
# Expander Uniform Gap Witness
Category: Frontier Spectral
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Matrix

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

/-! ## The hypercube graph -/

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2


lemma flipAt_zero_cons {k : ℕ} (a : ZMod 2) (y : Cube k) :
    flipAt 0 (Fin.cons a y) = Fin.cons (a + 1) y := by
  funext j
  induction j using Fin.cases with
  | zero => simp [flipAt]
  | succ i =>
    rw [flipAt_apply_of_ne (Fin.succ_ne_zero i), Fin.cons_succ, Fin.cons_succ]

