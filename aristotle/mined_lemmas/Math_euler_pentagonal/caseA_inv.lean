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

lemma caseA_inv (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hne2 : mn S ≠ mx S - mn S + 1) : franklin (franklin S) = S := by
  have hmx := caseA_mx hA
  have hst := caseA_stair hne h0 hA hne2
  have hmn := caseA_mn hne hA
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ mn S := one_le_mn hne h0
  have h2 : mn S ≤ mx S := le_mx hm
  have ht' := caseA_top_mem_erase hne h0 hA hne2
  rw [caseB_franklin (S := franklin S) (by omega), hmx, hst]
  have e1 : (franklin S).erase (mx S + 1) = (S.erase (mn S)).erase (mx S - mn S + 1) := by
    rw [caseA_franklin hA, Finset.erase_insert (caseA_succ_notMem)]
  have e2 : mx S + 1 - mn S = mx S - mn S + 1 := by omega
  rw [e1, e2, Finset.insert_erase ht', Finset.insert_erase hm]

