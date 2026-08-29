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
theorem sumset_lower_bound {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  set S := (A.image (· + B.min' hB)) ∪ (B.image (A.max' hA + ·)) with hS
  have hcard1 : (A.image (· + B.min' hB)).card = A.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hcard2 : (B.image (A.max' hA + ·)).card = B.card :=
    Finset.card_image_of_injective _ (add_right_injective _)
  have hunion : S.card + 1 = A.card + B.card := by
    have := Finset.card_union_add_card_inter (A.image (· + B.min' hB))
      (B.image (A.max' hA + ·))
    rw [witness_inter hA hB, hcard1, hcard2] at this
    simpa [hS] using this
  have hsub : S.card ≤ (A + B).card :=
    Finset.card_le_card (witness_subset_sumset hA hB)
  omega

end AdditiveComb

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

