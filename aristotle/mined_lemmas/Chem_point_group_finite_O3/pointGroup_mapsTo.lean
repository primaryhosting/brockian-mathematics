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

/-- The orthogonal group `O(3)`, realized as the group of `3 × 3` real orthogonal matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The **molecular point group** of a molecule whose nuclei occupy the finite set of
positions `S ⊆ ℝ³` (with the centre of mass at the origin): the subgroup of `O(3)`
consisting of those orthogonal transformations that map the set of nuclear positions
onto itself. -/

theorem pointGroup_mapsTo {S : Finset (Fin 3 → ℝ)} {M : ↥O3} (hM : M ∈ pointGroup S)
    {v : Fin 3 → ℝ} (hv : v ∈ S) : (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v ∈ S :=
  (hM v).2 hv

/-- **Every molecular point group is a finite subgroup of `O(3)`.**

By construction `Chem.pointGroup S` is a subgroup of the orthogonal group `O(3)`; the content
of the statement is that it is *finite*, whenever the nuclear positions `S` are finitely many
and are not all contained in a proper subspace of `ℝ³` (i.e. they span `ℝ³`, which holds for
any genuinely three-dimensional molecule).  Indeed, a symmetry operation is determined by its
action on a spanning set, so restriction gives an injection of the point group into the
(finite) set of self-maps of the nuclear positions. -/
