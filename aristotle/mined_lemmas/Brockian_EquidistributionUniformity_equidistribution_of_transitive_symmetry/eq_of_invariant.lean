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

theorem eq_of_invariant [MulAction.IsPretransitive G X]
    {w : X → ℝ} (hw : ∀ (g : G) (y : X), w (g • y) = w y) (x y : X) : w y = w x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  rw [← hg, hw]

omit [Fintype G] in
/-- A function invariant under a transitive symmetry group equals its own average:
it is *equidistributed* over the underlying set. -/
