/-
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The support of a nearest-neighbour bond gate sitting on the bond `i` of the
spin chain `ℤ`: the two sites `i` and `i + 1`. -/

theorem twoSiteNet_not_commutative :
    ∃ x y : SpinPairMat, x ∈ twoSiteNet.loc {0} ∧ y ∈ twoSiteNet.loc {0} ∧ x * y ≠ y * x := by
  refine ⟨(!![0, 1; 0, 0] : SpinMat) ⊗ₖ 1, (!![0, 0; 1, 0] : SpinMat) ⊗ₖ 1,
    ⟨_, _, rfl, fun h => absurd rfl h, fun _ => rfl⟩,
    ⟨_, _, rfl, fun h => absurd rfl h, fun _ => rfl⟩, ?_⟩
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  intro h
  have := congrFun (congrFun h (0, 0)) (0, 0)
  simp [Matrix.kroneckerMap, Matrix.mul_apply, Fin.sum_univ_succ] at this

end Frontier

