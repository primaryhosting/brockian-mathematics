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


lemma flipAt_injective {k : ℕ} (x : Cube k) :
    Function.Injective (fun i : Fin k => flipAt i x) := by
  intro i j h
  by_contra hij
  have h1 : flipAt i x j = flipAt j x j := congrFun h j
  rw [flipAt_apply_of_ne (Ne.symm hij), flipAt_apply_self] at h1
  exact zmod_two_succ_ne (x j) h1.symm

/-- The `k`-dimensional hypercube graph `Q_k`: two binary strings are adjacent iff they
differ in exactly one coordinate. -/
