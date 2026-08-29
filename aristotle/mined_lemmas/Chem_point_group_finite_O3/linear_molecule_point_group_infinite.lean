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

theorem linear_molecule_point_group_infinite :
    Infinite (pointGroup ({Pi.single 2 (1 : ℝ)} : Finset (Fin 3 → ℝ))) := by
  have hmem : ∀ t : ℝ, (⟨rotZ t, rotZ_mem_O3 t⟩ : O3) ∈
      pointGroup ({Pi.single 2 (1 : ℝ)} : Finset (Fin 3 → ℝ)) := by
    intro t x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [Finset.mem_singleton, act_rotZ_zAxis]
  refine Infinite.of_injective
    (fun n : ℕ => (⟨⟨rotZ (1 / (n + 1)), rotZ_mem_O3 _⟩, hmem _⟩ :
      pointGroup ({Pi.single 2 (1 : ℝ)} : Finset (Fin 3 → ℝ)))) ?_
  intro n m hnm
  have h : rotZ (1 / ((n : ℝ) + 1)) = rotZ (1 / ((m : ℝ) + 1)) := by
    simpa using Subtype.ext_iff.mp (Subtype.ext_iff.mp hnm)
  have h1 : Real.cos (1 / ((n : ℝ) + 1)) = Real.cos (1 / ((m : ℝ) + 1)) := by
    have := congrFun (congrFun h 0) 0
    simpa [rotZ] using this
  have hb : ∀ k : ℕ, (1 : ℝ) / (k + 1) ∈ Set.Icc 0 Real.pi := by
    intro k
    refine ⟨by positivity, ?_⟩
    have h2 : (1 : ℝ) / (k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    linarith [Real.pi_gt_three]
  have heq := Real.injOn_cos (hb n) (hb m) h1
  have hpos : (0 : ℝ) < (n + 1) := by positivity
  have hpos' : (0 : ℝ) < (m + 1) := by positivity
  have hsucc : ((n : ℝ) + 1) = ((m : ℝ) + 1) := by
    field_simp at heq
    linarith
  have : (n : ℝ) = m := by linarith
  exact_mod_cast this

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

