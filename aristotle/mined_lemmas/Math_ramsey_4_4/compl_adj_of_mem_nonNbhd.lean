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

theorem compl_adj_of_mem_nonNbhd {T : Finset V} {v w : V} (h : w ∈ nonNbhd G T v) : Gᶜ.Adj v w := by
  rw [nonNbhd, Finset.mem_filter, Finset.mem_erase] at h
  exact ⟨fun hvw => h.1.1 hvw.symm, h.2⟩

