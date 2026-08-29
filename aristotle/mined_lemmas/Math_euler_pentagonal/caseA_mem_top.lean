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

lemma caseA_mem_top (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S) :
    mx S - mn S + 1 ∈ S := by
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ mn S := one_le_mn hne h0
  have h2 : mn S ≤ mx S := le_mx hm
  have hmem := mem_of_lt_stair (S := S) (i := mn S - 1) (by omega)
  have h3 : mx S - (mn S - 1) = mx S - mn S + 1 := by omega
  rwa [h3] at hmem

