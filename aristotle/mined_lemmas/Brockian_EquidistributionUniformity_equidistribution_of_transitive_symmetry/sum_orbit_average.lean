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

theorem sum_orbit_average (f : X → ℝ) :
    (∑ x : X, ∑ g : G, f (g • x)) = Fintype.card G * ∑ x : X, f x := by
  rw [Finset.sum_comm]
  have : ∀ g : G, (∑ x : X, f (g • x)) = ∑ x : X, f x := by
    intro g
    exact Fintype.sum_bijective (fun x => g • x) (MulAction.bijective g) _ _ (fun _ => rfl)
  simp [this, Finset.sum_const, mul_comm]

/-- **Equidistribution of transitive symmetry.**  If a finite group `G` acts transitively on a
finite set `X`, then for every real-valued function `f` on `X` and every point `x`, the average
of `f` over the group orbit of `x` (counted with multiplicity over `G`) equals the average of
`f` over all of `X`.  Equivalently, the orbit of any point is equidistributed in `X`. -/
