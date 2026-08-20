/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Chem

open Matrix

/-- The point group of a molecule, modelled as a finite set `S` of atomic positions in
`ℝ³`: it is the subgroup of the orthogonal group `O(3)` consisting of those orthogonal
transformations that map the molecule onto itself. -/

theorem point_group_card_le (S : Finset (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) :
    Nat.card (pointGroup S) ≤ S.card ^ S.card := by
  have := Nat.card_le_card_of_injective (atomMap S) (atomMap_injective hspan)
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using this

/-- The elements of a point group really are orthogonal transformations: they preserve
the Euclidean inner product on `ℝ³`. -/
