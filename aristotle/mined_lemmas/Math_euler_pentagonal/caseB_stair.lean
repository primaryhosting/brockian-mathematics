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

lemma caseB_stair (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : stair S ≤ stair (franklin S) := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have hlt := caseB_lt hne h0 hB hne2
  have hmx := caseB_mx hne h0 hB hne2
  refine le_stair (caseB_zero hne h0 hB hne2) ?_
  intro i hi
  rw [hmx, caseB_franklin hB]
  rcases Nat.lt_or_ge (i + 1) (stair S) with h | h
  · have hmS : mx S - (i + 1) ∈ S := mem_of_lt_stair h
    have heq : mx S - 1 - i = mx S - (i + 1) := by omega
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_erase.2 ⟨by omega, hmS⟩))
  · have heq : mx S - 1 - i = mx S - stair S := by omega
    rw [heq]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

