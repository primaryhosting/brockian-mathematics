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

theorem eq_of_act_eq_on_span {S : Finset (Fin 3 → ℝ)}
    (hspan : Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤) {A B : O3}
    (h : ∀ x ∈ S, act A x = act B x) : A = B := by
  have hlin : Matrix.toLin' (A : Matrix (Fin 3) (Fin 3) ℝ)
      = Matrix.toLin' (B : Matrix (Fin 3) (Fin 3) ℝ) := by
    refine LinearMap.ext_on hspan ?_
    intro x hx
    simpa [Matrix.toLin'_apply, act] using h x hx
  have : (A : Matrix (Fin 3) (Fin 3) ℝ) = (B : Matrix (Fin 3) (Fin 3) ℝ) :=
    Matrix.toLin'.injective hlin
  exact Subtype.ext this

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

For a molecule given by a finite set `S` of atomic positions spanning `ℝ³` (i.e. a
non-linear molecule), the point group `pointGroup S` is, by construction, a subgroup of the
orthogonal group `O(3)`, and it is finite. -/
