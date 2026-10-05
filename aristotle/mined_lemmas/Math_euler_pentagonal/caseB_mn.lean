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

lemma caseB_mn (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : mn (franklin S) = stair S := by
  have hlt := caseB_lt hne h0 hB hne2
  have hmem : stair S ∈ franklin S := by
    rw [caseB_franklin hB]; exact Finset.mem_insert_self _ _
  refine le_antisymm (mn_le hmem) ?_
  have hall : ∀ x ∈ franklin S, stair S ≤ x := by
    intro x hx
    rw [caseB_franklin hB] at hx
    rcases Finset.mem_insert.1 hx with h | h
    · omega
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · have := mn_le (Finset.mem_of_mem_erase h)
      omega
  exact hall _ (mn_mem ⟨_, hmem⟩)

