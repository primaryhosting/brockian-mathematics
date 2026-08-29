/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: binary strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The `i`-th standard basis vector of the cube (the string with a single `1`, at `i`). -/

lemma basisVec_apply_self {k : ℕ} (i : Fin k) : basisVec i i = 1 := by
  simp [basisVec]

