/-
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Ko Rado
Category: Frontier Math
Target: Math2.erdos_ko_rado
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Math2

open Finset

/-- The canonical map sending a set of naturals to the corresponding set of elements of
`Fin n`, keeping exactly the elements that are `< n`. -/

lemma image_val_toFinSet {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n) :
    (toFinSet n A).image (Fin.val) = A := by
  ext x
  simp only [Finset.mem_image, mem_toFinSet]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro hx
    have hxn : x < n := Finset.mem_range.mp (hA hx)
    exact ⟨⟨x, hxn⟩, hx, rfl⟩

