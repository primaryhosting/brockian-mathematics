/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem nbhd_eq_filter (T : Finset V) (v : V) : nbhd G T v = T.filter (fun w => G.Adj v w) := by
  ext w
  simp only [nbhd, Finset.mem_filter, Finset.mem_erase]
  constructor
  · tauto
  · rintro ⟨hw, hadj⟩
    exact ⟨⟨fun h => G.irrefl (h ▸ hadj), hw⟩, hadj⟩

