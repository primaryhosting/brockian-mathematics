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

theorem nonNbhd_eq_compl_nbhd {T : Finset V} {v : V} :
    nonNbhd G T v = nbhd Gᶜ T v := by
  ext w
  simp only [nonNbhd, nbhd, Finset.mem_filter, Finset.mem_erase, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h1.1 h.symm, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.2⟩

/-- Extending a clique contained in the neighbourhood of `v` by the vertex `v` itself. -/
