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


namespace Chem

open Matrix

/-- The point group of a molecule, modelled as a finite set `S` of atomic positions in
`ℝ³`: it is the subgroup of the orthogonal group `O(3)` consisting of those orthogonal
transformations that map the molecule onto itself. -/

theorem span_unitVectors :
    Submodule.span ℝ ((({Pi.single 0 1, Pi.single 1 1, Pi.single 2 1} :
      Finset (Fin 3 → ℝ))) : Set (Fin 3 → ℝ)) = ⊤ := by
  have hb := (Pi.basisFun ℝ (Fin 3)).span_eq
  rw [← hb]
  congr 1
  ext x
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
    Set.mem_singleton_iff, Set.mem_range, Pi.basisFun_apply]
  constructor
  · rintro (h | h | h) <;> subst h
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

/-- An instance of the theorem: the point group of the "molecule" consisting of the three
unit vectors along the coordinate axes is finite. -/
example : Finite (pointGroup {Pi.single 0 1, Pi.single 1 1, Pi.single 2 1}) :=
  point_group_finite_O3 _ span_unitVectors

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

