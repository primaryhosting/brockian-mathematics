/-
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The eight Thurston geometries

We formalize a *model geometry* as a topological space `X` together with a group `G`
acting on `X` by homeomorphisms, transitively.  A closed 3-manifold `M` is *geometric*,
modelled on `(X, G)`, when `M` is homeomorphic to a quotient `X / Γ` for a subgroup
`Γ ≤ G` acting freely and properly discontinuously.

The eight Thurston geometries are realized below by concrete model spaces:

* `E³`      : `ℝ³` acted on by translations;
* `S³`      : the unit sphere in `ℝ⁴` acted on by linear isometries;
* `H³`      : the solvable Lie group `ℝ² ⋊ ℝ` (`t` acting by `e^t` on both factors),
              which carries a left invariant metric of constant curvature `-1`;
* `S² × ℝ`  : the unit sphere in `ℝ³` times `ℝ`;
* `H² × ℝ`  : the group `(ℝ ⋊ ℝ) × ℝ`, the affine group of the line (a model of `H²`)
              times `ℝ`;
* `SL(2,ℝ)~`: the universal cover of `PSL(2,ℝ)`, realized as the group of lifts to `ℝ`
              of the projective action of `SL(2,ℝ)` on directions of `ℝ²`;
* `Nil`     : the Heisenberg group;
* `Sol`     : the solvable group `ℝ² ⋊ ℝ` (`t` acting by `e^t`, `e^{-t}`).

In each case the group of the geometry is taken to be a transitive group of isometries
of the model space (for the Lie group models: the group acting on itself by left
translations); we do not verify maximality of these groups, which is what singles out
the eight geometries among all homogeneous 3-dimensional spaces.
-/

/-- Labels for the eight Thurston geometries. -/
inductive ThurstonGeometry
  | euclidean
  | spherical
  | hyperbolic
  | sphereProdLine
  | hyperbolicProdLine
  | slTwoTilde
  | nil
  | sol
  deriving DecidableEq, Fintype, Repr

/-! ### Euclidean 3-space as a group -/

/-- Euclidean 3-space, viewed as the group of its own translations. -/

lemma continuous_pair : Continuous (fun p : SLTilde => (p.toFun, p.invFun)) :=
  continuous_induced_dom

instance : Mul SLTilde where
  mul p q :=
  { toFun := p.toFun.comp q.toFun
    invFun := q.invFun.comp p.invFun
    left_inv := fun x => by simp [q.left_inv, p.left_inv]
    right_inv := fun x => by simp [q.right_inv, p.right_inv]
    isLift := by
      obtain ⟨A, hA⟩ := p.isLift
      obtain ⟨B, hB⟩ := q.isLift
      exact ⟨A * B, by simpa [ContinuousMap.coe_comp] using isSLLift_mul hA hB⟩ }

instance : One SLTilde where
  one := { toFun := ContinuousMap.id ℝ, invFun := ContinuousMap.id ℝ,
           left_inv := fun _ => rfl, right_inv := fun _ => rfl, isLift := ⟨1, isSLLift_one⟩ }

instance : Inv SLTilde where
  inv p :=
  { toFun := p.invFun, invFun := p.toFun, left_inv := p.right_inv, right_inv := p.left_inv
    isLift := by
      obtain ⟨A, hA⟩ := p.isLift
      exact ⟨A⁻¹, isSLLift_inv hA p.right_inv⟩ }

instance : Group SLTilde where
  mul_assoc a b c := by ext x <;> rfl
  one_mul a := by ext x <;> rfl
  mul_one a := by ext x <;> rfl
  inv_mul_cancel a := by ext x <;> exact a.left_inv x

