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

lemma caseA_ne {S : Finset ℕ} (hne : S.Nonempty) (h0 : 0 ∉ S) (hA : mn S ≤ stair S)
    (hexc : ¬ IsExc S) : mn S ≠ mx S - mn S + 1 := by
  intro heq
  have hm : mn S ∈ S := mn_mem hne
  have h1 : 1 ≤ mn S := Nat.one_le_iff_ne_zero.2 (fun h => h0 (h ▸ hm))
  have h2 : mn S ≤ mx S := le_mx hm
  refine hexc (Or.inr ⟨mn S, h1, Or.inl ?_⟩)
  have hMx : mx S = 2 * mn S - 1 := by omega
  ext x
  simp only [Finset.mem_Icc]
  constructor
  · exact fun hx => ⟨mn_le hx, by rw [← hMx]; exact le_mx hx⟩
  · rintro ⟨hx1, hx2⟩
    have hx2' : x ≤ mx S := by omega
    have : mx S - (mx S - x) ∈ S := mem_of_lt_stair (by omega)
    have heq2 : mx S - (mx S - x) = x := by omega
    rwa [heq2] at this

/-- If `S` is not exceptional and we are in the second Franklin case, the move is legal. -/
