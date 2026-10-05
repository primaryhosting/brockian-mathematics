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

lemma caseB_card (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : (franklin S).card = S.card + 1 := by
  have h1 : 1 ≤ S.card := Finset.card_pos.2 hne
  rw [caseB_franklin hB, Finset.card_insert_of_notMem (caseB_ins_notMem hne h0 hB hne2),
    Finset.card_insert_of_notMem (caseB_sub_notMem h0), Finset.card_erase_of_mem (mx_mem hne)]
  omega

