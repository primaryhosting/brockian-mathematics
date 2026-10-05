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

lemma caseB_ins_notMem (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) :
    stair S ∉ insert (mx S - stair S) (S.erase (mx S)) := by
  have hlt := caseB_lt hne h0 hB hne2
  intro h
  rcases Finset.mem_insert.1 h with h | h
  · omega
  · exact caseB_stair_notMem hB (Finset.mem_of_mem_erase h)

