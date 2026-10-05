import Mathlib

/-!
# Euler Pentagonal
Category: Pure Mathematics
Target: Math.euler_pentagonal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Math

/-! ## Distinct partitions as finsets of positive integers -/

/-- The finset of all "partitions of `n` into distinct parts", encoded as finsets of
positive integers whose sum is `n`. -/

lemma caseA_zero (h0 : 0 ∉ S) (hA : mn S ≤ stair S) : 0 ∉ franklin S := by
  rw [caseA_franklin hA]
  intro h
  rcases Finset.mem_insert.1 h with h | h
  · omega
  · exact h0 (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))

