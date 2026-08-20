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


@[simp] lemma flipAt_flipAt {k : ℕ} (i : Fin k) (x : Cube k) :
    flipAt i (flipAt i x) = x := by
  funext j
  by_cases h : j = i
  · subst h
    rw [flipAt_apply_self, flipAt_apply_self, zmod_two_succ_succ]
  · rw [flipAt_apply_of_ne h, flipAt_apply_of_ne h]

