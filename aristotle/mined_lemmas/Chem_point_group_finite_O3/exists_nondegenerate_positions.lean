/-
# Point Group Finite O 3
Category: Chemistry
Target: Chem.point_group_finite_O3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`: the group of real `3 × 3` matrices `A` with `Aᵀ * A = 1`,
acting on Euclidean three-space `Fin 3 → ℝ`. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) :=
  Matrix.orthogonalGroup (Fin 3) ℝ

/-- The action of an element of `O(3)` on a point of Euclidean three-space. -/

theorem exists_nondegenerate_positions :
    ∃ S : Finset (Fin 3 → ℝ), Submodule.span ℝ (S : Set (Fin 3 → ℝ)) = ⊤ := by
  refine ⟨Finset.univ.image (fun i : Fin 3 => (Pi.basisFun ℝ (Fin 3)) i), ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact (Pi.basisFun ℝ (Fin 3)).span_eq

end Chem

