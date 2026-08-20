import Mathlib

/-!
# Molecular point groups are finite subgroups of O(3)

A molecule is modelled by the set `S ⊆ ℝ³` of its nuclear positions, placed so that the
centre of mass sits at the origin.  Its *point group* is the group of all orthogonal
transformations of `ℝ³` mapping the molecule onto itself; by construction this is a
subgroup of `O(3)` (here realised as the group `Matrix.orthogonalGroup (Fin 3) ℝ` of real
orthogonal `3 × 3` matrices acting on `Fin 3 → ℝ` by `mulVec`).

The main theorem `Chem.point_group_finite_O3` shows that this subgroup is finite for every
molecule with finitely many atoms whose positions span `ℝ³`.  The spanning hypothesis
cannot be dropped: a linear molecule such as CO₂ has the infinite point group `D∞h`
(all rotations about the molecular axis are symmetries).
-/

namespace Chem

open Matrix

/-- The orthogonal group `O(3)`, realised as real orthogonal `3 × 3` matrices. -/
abbrev O3 : Submonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.orthogonalGroup (Fin 3) ℝ

/-- The natural action of `O(3)` on `ℝ³`. -/

theorem pointGroup_diatomic_infinite : Infinite (pointGroup diatomic) := by
  have hinj : Function.Injective
      (fun n : ℕ => (⟨rotZ (1 / (n + 1)), rotZ_mem _⟩ : pointGroup diatomic)) := by
    intro n m h
    have h' : Real.cos (1 / ((n : ℝ) + 1)) = Real.cos (1 / ((m : ℝ) + 1)) := by
      have h2 := congrArg
        (fun A : pointGroup diatomic => ((A : O3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0) h
      simpa [rotZ] using h2
    have hb : ∀ k : ℕ, (1 : ℝ) / (k + 1) ∈ Set.Icc 0 Real.pi := by
      intro k
      refine ⟨by positivity, ?_⟩
      have h1 : (1 : ℝ) / (k + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; simp
      linarith [Real.pi_gt_three]
    have heq := Real.injOn_cos (hb n) (hb m) h'
    have hnm : (n : ℝ) = m := by field_simp at heq; linarith
    exact_mod_cast hnm
  exact Infinite.of_injective _ hinj

end Chem

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

