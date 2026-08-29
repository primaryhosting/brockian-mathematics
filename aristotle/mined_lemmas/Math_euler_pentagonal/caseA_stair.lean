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

lemma caseA_stair (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : stair (franklin S) = mn S := by
  have hmx := caseA_mx hA
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ mn S := one_le_mn hne h0
  have h2 : mn S ≤ mx S := le_mx hm
  have hlt : mn S < mx S - mn S + 1 := caseA_lt hne h0 hA hne2
  refine le_antisymm ?_ ?_
  · refine stair_le ?_
    rw [hmx]
    have he : mx S + 1 - mn S = mx S - mn S + 1 := by omega
    rw [he, caseA_franklin hA]
    intro hmem
    rcases Finset.mem_insert.1 hmem with h | h
    · omega
    · exact (Finset.notMem_erase _ _) h
  · refine le_stair (caseA_zero h0 hA) ?_
    intro i hi
    rw [hmx, caseA_franklin hA]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp
    · have hmem : mx S - (i - 1) ∈ S := mem_of_lt_stair (by omega)
      have heq : mx S + 1 - i = mx S - (i - 1) := by omega
      rw [heq]
      exact Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨by omega, Finset.mem_erase.2 ⟨by omega, hmem⟩⟩)

