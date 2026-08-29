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

lemma caseB_zero (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : 0 ∉ franklin S := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have hlt := caseB_lt hne h0 hB hne2
  rw [caseB_franklin hB]
  intro h
  rcases Finset.mem_insert.1 h with h | h
  · omega
  rcases Finset.mem_insert.1 h with h | h
  · omega
  · exact h0 (Finset.mem_of_mem_erase h)

