/-
# Wiener Path Formula
Category: Chemistry
Target: Chem.wiener_path_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Finset

/-- The Wiener index of a finite graph: the sum of the graph distances over all
unordered pairs of vertices (equivalently, half the sum over all ordered pairs). -/

lemma sum_dist_to_top (n : ℕ) :
    ∑ i ∈ Finset.range n, Nat.dist i n = ∑ i ∈ Finset.range n, (i + 1) := by
  rw [← Finset.sum_range_reflect (fun i => i + 1) n]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Nat.dist]
  omega

