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

lemma chi_basisVec {k : ℕ} (S : Cube k) (i : Fin k) : chi S (basisVec i) = sgn (S i) := by
  unfold chi
  rw [Finset.prod_eq_single i]
  · rw [basisVec_apply_self, mul_one]
  · intro j _ hj
    simp [basisVec, hj, sgn_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

