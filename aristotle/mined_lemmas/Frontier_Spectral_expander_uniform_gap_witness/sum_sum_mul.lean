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


lemma sum_sum_mul {k : ℕ} (c : ℝ) (p : Cube k → Fin k → ℝ) :
    c * (∑ x : Cube k, ∑ i : Fin k, p x i) = ∑ x : Cube k, ∑ i : Fin k, c * p x i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _

