/-
# Sumset Lower Bound
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.sumset_lower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset Pointwise

namespace AdditiveComb

/-- The two "extremal translates" `A + {min B}` and `{max A} + B` meet in exactly one point. -/

lemma inter_translates (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.image (· + B.min' hB)) ∩ (B.image (A.max' hA + ·)) = {A.max' hA + B.min' hB} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have h1 : a ≤ A.max' hA := A.le_max' a ha
    have h2 : B.min' hB ≤ b := B.min'_le b hb
    omega
  · rintro rfl
    exact ⟨⟨A.max' hA, A.max'_mem hA, rfl⟩, ⟨B.min' hB, B.min'_mem hB, rfl⟩⟩

/-- **Sumset lower bound** (the Cauchy–Davenport analogue over `ℤ`, i.e. the base case of
Freiman's lemma): for nonempty finite sets of integers, `|A| + |B| - 1 ≤ |A + B|`. -/
