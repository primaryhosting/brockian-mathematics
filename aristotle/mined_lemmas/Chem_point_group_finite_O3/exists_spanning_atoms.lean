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

theorem exists_spanning_atoms :
    ∃ S : Finset (Fin 3 → ℝ), Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤ := by
  classical
  refine ⟨Finset.image (fun i : Fin 3 => Pi.single i (1 : ℝ)) Finset.univ, ?_⟩
  have hb := (Pi.basisFun ℝ (Fin 3)).span_eq
  convert hb using 2
  ext x
  simp [Set.range, Pi.basisFun_apply, eq_comm]

/-- Consequently there is at least one (finite) molecular point group. -/
example : ∃ S : Finset (Fin 3 → ℝ), Finite (pointGroup S) := by
  obtain ⟨S, hS⟩ := exists_spanning_atoms
  exact ⟨S, point_group_finite_O3 S hS⟩

/-! ### Sharpness: the non-linearity (spanning) hypothesis cannot be dropped

A linear molecule, modelled here by a single atom on the `z`-axis, is invariant under all
rotations about that axis, so its point group (`C∞v`) is infinite. -/

/-- The rotation of `ℝ³` by the angle `t` about the `z`-axis. -/
