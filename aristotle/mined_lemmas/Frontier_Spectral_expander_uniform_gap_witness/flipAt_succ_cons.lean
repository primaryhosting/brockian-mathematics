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


lemma flipAt_succ_cons {k : ℕ} (i : Fin k) (a : ZMod 2) (y : Cube k) :
    flipAt i.succ (Fin.cons a y) = Fin.cons a (flipAt i y) := by
  funext j
  induction j using Fin.cases with
  | zero =>
    rw [flipAt_apply_of_ne (Ne.symm (Fin.succ_ne_zero i)), Fin.cons_zero, Fin.cons_zero]
  | succ j =>
    by_cases hj : j = i
    · subst hj
      rw [flipAt_apply_self, Fin.cons_succ, Fin.cons_succ, flipAt_apply_self]
    · rw [flipAt_apply_of_ne (by simpa using hj), Fin.cons_succ, Fin.cons_succ,
        flipAt_apply_of_ne hj]

/-- The Dirichlet form on the `(k+1)`-cube decomposes along the first coordinate. -/
