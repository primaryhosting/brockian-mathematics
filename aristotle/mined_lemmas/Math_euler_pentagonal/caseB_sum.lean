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

lemma caseB_sum (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) :
    ∑ i ∈ franklin S, i = ∑ i ∈ S, i := by
  have h2 : stair S ≤ mx S := stair_le_mx h0
  rw [caseB_franklin hB, Finset.sum_insert (caseB_ins_notMem hne h0 hB hne2),
    Finset.sum_insert (caseB_sub_notMem h0)]
  have e1 : mx S + ∑ i ∈ S.erase (mx S), i = ∑ i ∈ S, i :=
    Finset.add_sum_erase S (fun i => i) (mx_mem hne)
  omega

