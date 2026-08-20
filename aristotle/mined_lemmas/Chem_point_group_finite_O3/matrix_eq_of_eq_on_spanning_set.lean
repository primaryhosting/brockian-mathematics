/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix

/-- `O3` is the orthogonal group of `ℝ³`, realized as the group of `3 × 3` real orthogonal
matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- **Key intermediate lemma.** A linear map of `ℝ³` (given by a matrix) is determined by its
values on a spanning set of vectors. Chemically: a symmetry operation of a molecule is completely
determined by what it does to the (finitely many) nuclei, provided these span space. -/

theorem matrix_eq_of_eq_on_spanning_set
    {A B : Matrix (Fin 3) (Fin 3) ℝ} {S : Set (Fin 3 → ℝ)}
    (hspan : Submodule.span ℝ S = ⊤)
    (h : ∀ v ∈ S, A *ᵥ v = B *ᵥ v) : A = B := by
  have hlin : A.mulVecLin = B.mulVecLin := LinearMap.ext_on hspan h
  exact Matrix.toLin'.injective hlin

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

A molecule is modelled by a finite set `S` of nuclear positions in `ℝ³` which is not contained in
any plane through the origin (i.e. `S` spans `ℝ³`); this non-degeneracy is exactly what excludes
the infinite point groups `C∞v`, `D∞h` of linear molecules.  Its point group is any subgroup `G`
of the orthogonal group `O(3)` all of whose elements permute the nuclei, i.e. map `S` into itself.
The conclusion is that `G` is finite.

The proof uses `matrix_eq_of_eq_on_spanning_set`: restricting a symmetry operation to `S` gives an
injection of `G` into the (finite) set of self-maps of `S`. -/
