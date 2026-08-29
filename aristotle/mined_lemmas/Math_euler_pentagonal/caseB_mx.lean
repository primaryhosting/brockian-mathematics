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

lemma caseB_mx (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hne2 : mx S ≠ 2 * stair S) : mx (franklin S) = mx S - 1 := by
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : stair S ≤ mx S := stair_le_mx h0
  have hlt := caseB_lt hne h0 hB hne2
  have hmem : mx S - 1 ∈ franklin S := by
    rw [caseB_franklin hB]
    rcases Nat.lt_or_ge 1 (stair S) with h | h
    · have hmS : mx S - 1 ∈ S := mem_of_lt_stair (S := S) (i := 1) h
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨by omega, hmS⟩))
    · have : mx S - stair S = mx S - 1 := by omega
      rw [← this]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  refine le_antisymm ?_ (le_mx hmem)
  have hall : ∀ x ∈ franklin S, x ≤ mx S - 1 := by
    intro x hx
    rw [caseB_franklin hB] at hx
    rcases Finset.mem_insert.1 hx with h | h
    · omega
    rcases Finset.mem_insert.1 h with h | h
    · omega
    · have hxS : x ∈ S := Finset.mem_of_mem_erase h
      have hxne : x ≠ mx S := (Finset.mem_erase.1 h).1
      have := le_mx hxS
      omega
  exact hall _ (mx_mem ⟨_, hmem⟩)

