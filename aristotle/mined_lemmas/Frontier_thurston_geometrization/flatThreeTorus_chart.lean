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

theorem flatThreeTorus_chart (x : Euc3) :
    ∃ U : Set FlatThreeTorus, IsOpen U ∧ torusProj x ∈ U ∧
      Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin 3)) := by
  have hBopen : IsOpen (Metric.ball x (1/2) : Set Euc3) := Metric.isOpen_ball
  set f : (Metric.ball x (1/2) : Set Euc3) → FlatThreeTorus := fun b => torusProj (b : Euc3)
    with hf
  have hcont : Continuous f := continuous_torusProj.comp continuous_subtype_val
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (lattice_inj_of_mem_ball x a b a.2 b.2 hab)
  have hopen : IsOpenMap f := by
    intro V hV
    have himg : f '' V = torusProj '' (Subtype.val '' V) := by rw [Set.image_image]
    rw [himg]
    exact isOpenMap_torusProj _ (hBopen.isOpenMap_subtype_val V hV)
  have hemb : Topology.IsOpenEmbedding f := .of_continuous_injective_isOpenMap hcont hinj hopen
  refine ⟨Set.range f, hemb.isOpen_range, ⟨⟨x, Metric.mem_ball_self (by norm_num)⟩, rfl⟩, ?_⟩
  exact ⟨(hemb.isEmbedding.toHomeomorph.symm).trans
    ((ballHomeoSpace x (1/2) (by norm_num)).trans euc3HomeoEuclidean)⟩

