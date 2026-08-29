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

lemma caseB_lt (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : stair S < mx S - stair S := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have h3 : mn S ≤ mx S - stair S + 1 := mn_le_mx_sub_stair hne h0
  omega

