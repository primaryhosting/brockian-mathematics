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

lemma caseA_card (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) :
    (franklin S).card + 1 = S.card := by
  have hm : mn S ∈ S := mn_mem hne
  have ht : mx S - mn S + 1 ∈ S := caseA_mem_top hne h0 hA
  have ht' := caseA_top_mem_erase hne h0 hA hne2
  have h2 : 2 ≤ S.card :=
    Finset.one_lt_card.2 ⟨mn S, hm, mx S - mn S + 1, ht, hne2⟩
  rw [caseA_franklin hA, Finset.card_insert_of_notMem (caseA_succ_notMem),
    Finset.card_erase_of_mem ht', Finset.card_erase_of_mem hm]
  omega

