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

lemma caseA_sum (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) :
    ∑ i ∈ franklin S, i = ∑ i ∈ S, i := by
  have hm : mn S ∈ S := mn_mem hne
  have h2 : mn S ≤ mx S := le_mx hm
  have ht' := caseA_top_mem_erase hne h0 hA hne2
  rw [caseA_franklin hA, Finset.sum_insert (caseA_succ_notMem)]
  have e1 : mn S + ∑ i ∈ S.erase (mn S), i = ∑ i ∈ S, i :=
    Finset.add_sum_erase S (fun i => i) hm
  have e2 : (mx S - mn S + 1) + ∑ i ∈ (S.erase (mn S)).erase (mx S - mn S + 1), i
      = ∑ i ∈ S.erase (mn S), i := Finset.add_sum_erase _ (fun i => i) ht'
  omega

