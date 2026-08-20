/-
# Cantor No Surjection
Category: Frontier — Set Theory
Target: Infinity.cantor_no_surjection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Infinity

/-- Key intermediate lemma: for any `f : X → Set X`, the diagonal set
`{x | x ∉ f x}` is not in the range of `f`. -/

theorem diagonal_not_mem_range {X : Type*} (f : X → Set X) :
    {x : X | x ∉ f x} ∉ Set.range f := by
  rintro ⟨a, ha⟩
  have : a ∈ f a ↔ a ∉ f a := by
    constructor
    · intro h
      have : a ∈ {x : X | x ∉ f x} := ha ▸ h
      exact this
    · intro h
      have : a ∈ {x : X | x ∉ f x} := h
      exact ha ▸ this
  tauto

/-- Cantor's theorem: no function `f : X → Set X` is surjective. -/
