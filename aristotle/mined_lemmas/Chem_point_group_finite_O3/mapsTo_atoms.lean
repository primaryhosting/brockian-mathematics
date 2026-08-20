import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Molecular point groups are finite subgroups of O(3)

A *molecule* is modelled as an assignment of an atomic number to each point of
Euclidean 3-space, with only finitely many points carrying an atom (the atoms),
placed so that the atoms are not all contained in a single line through the
origin (equivalently, the linear span of the atom positions has dimension at
least 2).  As is standard in chemistry, the origin is taken to be the fixed
point common to all symmetry operations (e.g. the centre of mass).

The *point group* of the molecule is the group of all linear isometries of
Euclidean 3-space (i.e. elements of `O(3)`) that map every point to a point
carrying the same atomic number.  By construction this is a subgroup of `O(3)`;
the main theorem `Chem.point_group_finite_O3` shows that it is finite.

The hypothesis that the atoms do not all lie on one line through the origin is
necessary: for a linear molecule the corresponding group contains all rotations
about the molecular axis and is infinite (the point groups `C∞v`, `D∞h`).
-/

namespace Chem

/-- Euclidean three-space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The orthogonal group `O(3)`: the group of linear isometries of Euclidean
three-space onto itself. -/
abbrev O3 : Type := E3 ≃ₗᵢ[ℝ] E3

/-- A molecule: an atomic-number function on Euclidean three-space with finite
support (the atoms), whose atoms span a subspace of dimension at least `2`
(i.e. the atoms are not all on a single line through the origin). -/
structure Molecule where
  /-- `atomicNumber x` is the atomic number of the atom sitting at `x`
  (`0` meaning that there is no atom at `x`). -/
  atomicNumber : E3 → ℕ
  /-- A molecule has finitely many atoms. -/
  finite_support : (Function.support atomicNumber).Finite
  /-- The atoms are not all contained in a line through the origin. -/
  two_le_finrank :
    2 ≤ Module.finrank ℝ (Submodule.span ℝ (Function.support atomicNumber))

namespace Molecule

variable (M : Molecule)

/-- The set of positions occupied by atoms of the molecule. -/

lemma mapsTo_atoms {f : O3} (hf : f ∈ M.pointGroup) {x : E3} (hx : x ∈ M.atoms) :
    f x ∈ M.atoms := by
  have h := hf x
  simp only [atoms, Function.mem_support] at hx ⊢
  rw [h]
  exact hx

end Molecule

/-- A subgroup of `O(3)` which maps a fixed finite set `S` into itself is finite,
provided the linear span of `S` has dimension at least `2`. -/
