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

lemma caseB_notExc (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : ¬ IsExc (franklin S) := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have hlt := caseB_lt hne h0 hB hne2
  have hmx := caseB_mx hne h0 hB hne2
  have hmn := caseB_mn hne h0 hB hne2
  have hst := caseB_stair hne h0 hB hne2
  rintro (h | ⟨c, hc, h | h⟩)
  · have hmem : stair S ∈ franklin S := by
      rw [caseB_franklin hB]; exact Finset.mem_insert_self _ _
    rw [h] at hmem
    simp at hmem
  · have hle : c ≤ 2 * c - 1 := by omega
    have h3 : mn (franklin S) = c := by rw [h, mn_Icc hle]
    have h4 : mx (franklin S) = 2 * c - 1 := by rw [h, mx_Icc hle]
    omega
  · have hle : c + 1 ≤ 2 * c := by omega
    have h3 : mn (franklin S) = c + 1 := by rw [h, mn_Icc hle]
    have h5 : stair (franklin S) = c := by rw [h, stair_Icc hle (by omega)]; omega
    omega

end CaseB

/-! ### The cancellation -/

/-- The exceptional distinct partitions of `n`. -/
