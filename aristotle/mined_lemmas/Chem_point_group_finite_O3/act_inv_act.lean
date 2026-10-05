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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

/-- The orthogonal group `O(3)`, realized as the group of real `3 × 3` orthogonal matrices. -/
abbrev O3 : Type := ↥(Matrix.orthogonalGroup (Fin 3) ℝ)

/-- The natural action of `O(3)` on Euclidean 3-space. -/

@[simp] lemma act_inv_act (g : O3) (x : Fin 3 → ℝ) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- A molecule: a finite set of nuclear positions in Euclidean 3-space, each atom carrying a
species label (e.g. its atomic number). -/
structure Molecule where
  /-- The set of nuclear positions. -/
  atoms : Set (Fin 3 → ℝ)
  /-- A molecule has finitely many atoms. -/
  atoms_finite : atoms.Finite
  /-- The chemical species (say, atomic number) sitting at a given position. -/
  species : (Fin 3 → ℝ) → ℕ

/-- The molecular point group of `M`: the subgroup of `O(3)` consisting of those orthogonal
transformations which map the nuclear framework onto itself, preserving atomic species. -/
