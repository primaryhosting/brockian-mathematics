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

lemma witness_inter {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.image (· + B.min' hB)) ∩ (B.image (A.max' hA + ·)) = {A.max' hA + B.min' hB} := by
  ext x
  simp only [mem_inter, mem_image, mem_singleton]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hb'⟩⟩
    have h1 : a ≤ A.max' hA := A.le_max' a ha
    have h2 : B.min' hB ≤ b := B.min'_le b hb
    omega
  · rintro rfl
    exact ⟨⟨A.max' hA, A.max'_mem hA, rfl⟩, ⟨B.min' hB, B.min'_mem hB, rfl⟩⟩

/-- **Sumset lower bound over the integers** (the Cauchy–Davenport analogue / base case of
Freiman's lemma): for finite nonempty sets `A B` of integers,
`#A + #B - 1 ≤ #(A + B)`. -/
