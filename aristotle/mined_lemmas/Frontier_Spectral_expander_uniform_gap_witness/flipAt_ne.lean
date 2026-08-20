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


lemma flipAt_ne {k : ℕ} (i : Fin k) (x : Cube k) : flipAt i x ≠ x := by
  intro h
  have h1 := congrFun h i
  rw [flipAt_apply_self] at h1
  exact zmod_two_succ_ne (x i) h1

