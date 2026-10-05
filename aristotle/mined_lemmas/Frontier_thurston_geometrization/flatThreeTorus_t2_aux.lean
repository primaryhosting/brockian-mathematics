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

theorem flatThreeTorus_t2_aux (x y : Euc3) (hxy : torusProj x ≠ torusProj y) :
    ∃ U V : Set FlatThreeTorus, IsOpen U ∧ IsOpen V ∧ torusProj x ∈ U ∧ torusProj y ∈ V ∧
      Disjoint U V := by
  obtain ⟨ε, hε, hbound⟩ := lattice_separation x y hxy
  have hBx : IsOpen (Metric.ball x (ε/3) : Set Euc3) := Metric.isOpen_ball
  have hBy : IsOpen (Metric.ball y (ε/3) : Set Euc3) := Metric.isOpen_ball
  refine ⟨torusProj '' (Metric.ball x (ε/3)), torusProj '' (Metric.ball y (ε/3)),
    isOpenMap_torusProj _ hBx, isOpenMap_torusProj _ hBy,
    ⟨x, Metric.mem_ball_self (by linarith), rfl⟩,
    ⟨y, Metric.mem_ball_self (by linarith), rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
  obtain ⟨γ, hγ, hguv⟩ := exists_lattice_of_torusProj_eq huv.symm
  have h1 : dist (γ * x) y ≤ dist (γ * x) (γ * u) + dist (γ * u) y := dist_triangle _ _ _
  rw [Euc3.dist_mul_left] at h1
  have h2 : dist (γ * u) y = dist v y := by rw [show γ * u = v from hguv]
  have h3 : dist x u < ε/3 := by rw [dist_comm]; exact Metric.mem_ball.mp hu
  have h4 : dist v y < ε/3 := Metric.mem_ball.mp hv
  have h5 := hbound γ hγ
  rw [h2] at h1
  linarith

instance : T2Space FlatThreeTorus := by
  constructor
  intro p q hpq
  obtain ⟨x, rfl⟩ := torusProj_surjective p
  obtain ⟨y, rfl⟩ := torusProj_surjective q
  exact flatThreeTorus_t2_aux x y hpq

/-! ## Closed 3-manifolds and the geometrization statement -/

/-- The 2-torus. -/
