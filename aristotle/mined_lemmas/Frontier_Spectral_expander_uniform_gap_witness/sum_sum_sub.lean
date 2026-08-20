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


lemma sum_sum_sub {k : ℕ} (p q : Cube k → Fin k → ℝ) :
    (∑ x : Cube k, ∑ i : Fin k, p x i) - (∑ x : Cube k, ∑ i : Fin k, q x i)
      = ∑ x : Cube k, ∑ i : Fin k, (p x i - q x i) := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => (Finset.sum_sub_distrib _ _).symm

