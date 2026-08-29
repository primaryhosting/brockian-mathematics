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
