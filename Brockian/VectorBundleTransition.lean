import Mathlib.Topology.VectorBundle.Basic

/-!
# Transition laws from Mathlib vector-bundle cores

The complex-manifold references emphasize that bundle transition functions must satisfy identity,
inverse, and triple-overlap laws.  Rather than introducing a parallel Čech-cocycle structure, this
module exposes those laws directly from Mathlib's `VectorBundleCore` API.

This is infrastructure only.  A nontrivial Möbius fixture still requires a concrete open cover and
coordinate changes, and relating any such bundle to phase depth still requires a typed comparison.
-/

namespace Brockian.VectorBundleTransition

open Set

variable {R B F ι : Type*}
  [NontriviallyNormedField R] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace R F]

variable (Z : VectorBundleCore R B F ι)

/-- A coordinate change is the identity on its own chart. -/
theorem coordChange_self_apply (i : ι) {x : B} (hx : x ∈ Z.baseSet i) (v : F) :
    Z.coordChange i i x v = v :=
  Z.coordChange_self i x hx v

/-- Coordinate changes compose in the order dictated by a triple overlap. -/
theorem coordChange_triple_apply (i j k : ι) {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k) (v : F) :
    Z.coordChange j k x (Z.coordChange i j x v) = Z.coordChange i k x v :=
  Z.coordChange_comp i j k x hx v

/-- Reversing a coordinate change gives a left inverse on a nonempty overlap. -/
theorem coordChange_leftInverse_apply (i j : ι) {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) (v : F) :
    Z.coordChange j i x (Z.coordChange i j x v) = v := by
  rw [Z.coordChange_comp i j i x ⟨hx, hx.1⟩ v]
  exact Z.coordChange_self i x hx.1 v

/-- Reversing a coordinate change gives a right inverse on a nonempty overlap. -/
theorem coordChange_rightInverse_apply (i j : ι) {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) (v : F) :
    Z.coordChange i j x (Z.coordChange j i x v) = v := by
  rw [Z.coordChange_comp j i j x ⟨⟨hx.2, hx.1⟩, hx.2⟩ v]
  exact Z.coordChange_self j x hx.2 v

/-- The two overlap maps form a linear equivalence, with both inverse obligations discharged by
the bundle-core cocycle law. -/
noncomputable def coordChangeLinearEquiv (i j : ι) {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) : F ≃ₗ[R] F where
  toLinearMap := (Z.coordChange i j x).toLinearMap
  invFun := Z.coordChange j i x
  left_inv := coordChange_leftInverse_apply Z i j hx
  right_inv := coordChange_rightInverse_apply Z i j hx

end Brockian.VectorBundleTransition
