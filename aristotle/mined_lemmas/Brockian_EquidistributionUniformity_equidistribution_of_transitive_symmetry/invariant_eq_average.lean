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

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.EquidistributionUniformity

open scoped BigOperators

variable {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]

omit [Fintype G] [Fintype X] in
/-- A function invariant under a transitive symmetry group is constant. -/

theorem invariant_eq_average [MulAction.IsPretransitive G X]
    {w : X → ℝ} (hw : ∀ (g : G) (y : X), w (g • y) = w y) (x : X) :
    w x = (∑ y : X, w y) / Fintype.card X := by
  have hcard : (0 : ℝ) < Fintype.card X := by
    have : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
    exact_mod_cast this
  have hsum : (∑ y : X, w y) = Fintype.card X * w x := by
    rw [Finset.sum_congr rfl (fun y _ => eq_of_invariant (G := G) hw x y)]
    simp [Finset.sum_const, mul_comm]
  rw [hsum]
  field_simp

/-- The group-average of `f` along the orbit of a point has the same total mass as `f`. -/
