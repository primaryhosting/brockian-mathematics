import Mathlib

/-!
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Molecular point groups are finite subgroups of `O(3)`

A molecule is modelled as a finite set `S` of atomic positions in `ℝ³` (for a molecule
with several atomic species one takes `S` to be the positions of the atoms of one species,
or one works with the labelled version; the argument is identical).

Its *point group* is the set of orthogonal transformations of `ℝ³` mapping the molecule onto
itself.  By construction this is a subgroup of `O(3)`; the content of the theorem is that it
is *finite*, which holds exactly when the molecule is not linear, i.e. when the atomic
positions span `ℝ³`.  (For a linear molecule the point group is `C∞v` or `D∞h`, which is
infinite, so the spanning hypothesis cannot be dropped.)
-/

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`, realised as the group of real orthogonal `3 × 3` matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The action of an element of `O(3)` on a point of `ℝ³`. -/

theorem inv_mapsTo_of_mapsTo {S : Finset (Fin 3 → ℝ)} {A : O3}
    (hA : ∀ x ∈ S, act A x ∈ S) : ∀ x ∈ S, act A⁻¹ x ∈ S := by
  classical
  have himg : S.image (act A) = S := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      simp only [Finset.mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hA x hx
    · exact le_of_eq (Finset.card_image_of_injective S (act_injective A)).symm
  intro x hx
  rw [← himg] at hx
  simp only [Finset.mem_image] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [← hyx, act_inv_act]
  exact hy

/-- The **point group** of a molecule whose atoms sit at the (finitely many) positions `S`:
the subgroup of `O(3)` consisting of the orthogonal transformations that map the set of
atomic positions onto itself. -/
