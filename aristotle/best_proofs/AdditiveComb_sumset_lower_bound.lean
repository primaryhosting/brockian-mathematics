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
theorem sumset_lower_bound (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card - 1 ≤ (A + B).card := by
  set a0 := A.max' hA with ha0
  set b0 := B.min' hB with hb0
  set S : Finset ℤ := (A.image (· + b0)) ∪ (B.image (a0 + ·)) with hS
  have hsub : S ⊆ A + B := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
      exact Finset.add_mem_add ha (B.min'_mem hB)
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h
      exact Finset.add_mem_add (A.max'_mem hA) hb
  have hcardA : (A.image (· + b0)).card = A.card :=
    Finset.card_image_of_injective _ (add_left_injective b0)
  have hcardB : (B.image (a0 + ·)).card = B.card :=
    Finset.card_image_of_injective _ (add_right_injective a0)
  have hinter : ((A.image (· + b0)) ∩ (B.image (a0 + ·))).card = 1 := by
    rw [inter_translates A B hA hB, Finset.card_singleton]
  have hunion : S.card + ((A.image (· + b0)) ∩ (B.image (a0 + ·))).card
      = (A.image (· + b0)).card + (B.image (a0 + ·)).card :=
    Finset.card_union_add_card_inter _ _
  have hle : S.card ≤ (A + B).card := Finset.card_le_card hsub
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

