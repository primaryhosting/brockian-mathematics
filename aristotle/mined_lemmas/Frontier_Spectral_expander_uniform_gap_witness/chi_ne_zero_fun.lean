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

lemma chi_ne_zero_fun {k : ℕ} (S : Cube k) : chi S ≠ 0 := by
  intro h
  have := congrFun h 0
  simp only [Pi.zero_apply] at this
  have hpos : chi S (0 : Cube k) = 1 := by
    unfold chi
    simp [sgn_zero]
  rw [hpos] at this
  exact one_ne_zero this

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the smallest nonzero eigenvalue of the Laplacian matrix of the
hypercube graph `Q k` (on `2 ^ k` vertices) equals `2`.  In particular the family
`(Q k)` has a spectral gap of at least `2`, uniformly in `k`. -/
