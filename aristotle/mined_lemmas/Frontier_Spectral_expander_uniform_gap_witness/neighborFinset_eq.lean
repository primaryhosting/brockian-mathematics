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


lemma neighborFinset_eq {k : ℕ} (x : Cube k) :
    (hypercube k).neighborFinset x = Finset.image (fun i : Fin k => flipAt i x) Finset.univ := by
  ext y
  simp [SimpleGraph.mem_neighborFinset, eq_comm]

