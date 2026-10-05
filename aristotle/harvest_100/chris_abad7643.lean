/-
# Freiman Two A
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.freiman_two_A
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace AdditiveComb

open Finset
open scoped Pointwise

/-- Translates of `A` by its minimum lie in `A + A`. -/
private lemma image_add_min_subset (A : Finset ℤ) (hA : A.Nonempty) :
    A.image (· + A.min' hA) ⊆ A + A := by
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact Finset.add_mem_add ha (A.min'_mem hA)

/-- Translates of `A` by its maximum lie in `A + A`. -/
private lemma image_add_max_subset (A : Finset ℤ) (hA : A.Nonempty) :
    A.image (· + A.max' hA) ⊆ A + A := by
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact Finset.add_mem_add ha (A.max'_mem hA)

/-- The two translates `A + min A` and `A + max A` meet exactly in `{min A + max A}`. -/
private lemma inter_translates (A : Finset ℤ) (hA : A.Nonempty) :
    A.image (· + A.min' hA) ∩ A.image (· + A.max' hA) = {A.min' hA + A.max' hA} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, b, hb, hb'⟩
    have h1 : a ≤ A.max' hA := A.le_max' a ha
    have h2 : A.min' hA ≤ b := A.min'_le b hb
    omega
  · rintro rfl
    refine ⟨⟨A.max' hA, A.max'_mem hA, by ring⟩, ⟨A.min' hA, A.min'_mem hA, by ring⟩⟩

/-- **Basic doubling bound.** For a finite nonempty set `A` of integers,
`2 * |A| - 1 ≤ |A + A|`. -/
theorem freiman_two_A (A : Finset ℤ) (hA : A.Nonempty) :
    2 * A.card - 1 ≤ (A + A).card := by
  set S : Finset ℤ := A.image (· + A.min' hA) with hS
  set T : Finset ℤ := A.image (· + A.max' hA) with hT
  have hScard : S.card = A.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hTcard : T.card = A.card :=
    Finset.card_image_of_injective _ (add_left_injective _)
  have hinter : (S ∩ T).card = 1 := by
    rw [hS, hT, inter_translates A hA]
    simp
  have hunion : (S ∪ T).card + 1 = 2 * A.card := by
    have := Finset.card_union_add_card_inter S T
    rw [hinter, hScard, hTcard] at this
    omega
  have hsub : S ∪ T ⊆ A + A := by
    refine Finset.union_subset ?_ ?_
    · exact image_add_min_subset A hA
    · exact image_add_max_subset A hA
  have := Finset.card_le_card hsub
  omega

end AdditiveComb

