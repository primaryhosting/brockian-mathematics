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

lemma caseB_ne {S : Finset ℕ} (hne : S.Nonempty) (h0 : 0 ∉ S) (hB : stair S < mn S)
    (hexc : ¬ IsExc S) : mx S ≠ 2 * stair S := by
  intro heq
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ stair S := stair_pos hne h0
  have h2 : mn S ≤ mx S := le_mx hm
  have h3 : mn S ≤ mx S - stair S + 1 := mn_le_mx_sub_stair hne h0
  refine hexc (Or.inr ⟨stair S, h1, Or.inr ?_⟩)
  ext x
  simp only [Finset.mem_Icc]
  constructor
  · exact fun hx => ⟨by have := mn_le hx; omega, by rw [← heq]; exact le_mx hx⟩
  · rintro ⟨hx1, hx2⟩
    have : mx S - (mx S - x) ∈ S := mem_of_lt_stair (by omega)
    have heq2 : mx S - (mx S - x) = x := by omega
    rwa [heq2] at this

