/-
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Expander Uniform Gap Witness
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.expander_uniform_gap_witness
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

open Finset Matrix

/-- The vertex set of the `k`-dimensional hypercube: bit strings of length `k`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- The hypercube `Q_k` has `2 ^ k` vertices. -/

lemma eig_eq_zero_iff {k : ℕ} (y : Cube k) : eig y = 0 ↔ y = 0 := by
  constructor
  · intro h
    by_contra hy
    have := two_le_eig hy
    rw [h] at this
    norm_num at this
  · rintro rfl
    simp [eig, sgn]

/-- **Uniform spectral gap for the hypercube family.**
For every `k ≥ 1`, the Laplacian of the hypercube graph `Q_k` on `2 ^ k` vertices has
`2` as an eigenvalue, and every nonzero eigenvalue is at least `2`; i.e. the smallest
nonzero Laplacian eigenvalue of `Q_k` equals `2`, uniformly in `k`. -/
