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

lemma caseB_inv (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : franklin (franklin S) = S := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have hlt := caseB_lt hne h0 hB hne2
  have hmx := caseB_mx hne h0 hB hne2
  have hmn := caseB_mn hne h0 hB hne2
  have hst := caseB_stair hne h0 hB hne2
  rw [caseA_franklin (S := franklin S) (by omega), hmx, hmn]
  have e1 : mx S - 1 + 1 = mx S := by omega
  have e2 : mx S - 1 - stair S + 1 = mx S - stair S := by omega
  rw [e1, e2]
  have e3 : (franklin S).erase (stair S) = insert (mx S - stair S) (S.erase (mx S)) := by
    rw [caseB_franklin hB, Finset.erase_insert (caseB_ins_notMem hne h0 hB hne2)]
  rw [e3, Finset.erase_insert (caseB_sub_notMem h0), Finset.insert_erase (mx_mem hne)]

