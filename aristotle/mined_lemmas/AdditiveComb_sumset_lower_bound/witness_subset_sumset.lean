import Mathlib

/-!
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

open Finset Pointwise

/-- The set `(A + min B) ∪ (max A + B)` is contained in the sumset `A + B`. -/

lemma witness_subset_sumset {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.image (· + B.min' hB)) ∪ (B.image (A.max' hA + ·)) ⊆ A + B := by
  intro x hx
  simp only [mem_union, mem_image] at hx
  rcases hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
  · exact Finset.add_mem_add ha (B.min'_mem hB)
  · exact Finset.add_mem_add (A.max'_mem hA) hb

/-- The two translates `A + min B` and `max A + B` meet exactly in `max A + min B`. -/
