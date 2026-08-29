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

lemma wt_basisVec {k : ℕ} (i : Fin k) : wt (basisVec i) = 1 := by
  classical
  unfold wt
  rw [show (Finset.univ.filter (fun j => basisVec i j ≠ 0)) = {i} by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hj
      exact h (by simp [basisVec, hj])
    · rintro rfl
      rw [basisVec_apply_self]
      exact one_ne_zero]
  simp

