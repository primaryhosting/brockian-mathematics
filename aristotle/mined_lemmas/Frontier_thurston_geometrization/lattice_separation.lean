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

theorem lattice_separation (x y : Euc3) (h : torusProj x ≠ torusProj y) :
    ∃ ε > 0, ∀ γ ∈ latticeSubgroup, ε ≤ dist (γ * x) y := by
  have hne : ∀ γ ∈ latticeSubgroup, γ * x ≠ y := by
    intro γ hγ hxy
    exact h ((torusProj_mul hγ x).symm.trans (congrArg torusProj hxy))
  have hK : IsCompact (insert x (Metric.closedBall y 1) : Set Euc3) :=
    (isCompact_closedBall y 1).insert x
  have hS := lattice_properlyDiscontinuous _ hK
  have hA : {γ : Euc3 | γ ∈ latticeSubgroup ∧ dist (γ * x) y ≤ 1}.Finite := by
    refine hS.subset ?_
    rintro γ ⟨hγ, hd⟩
    exact ⟨hγ, x, Set.mem_insert _ _,
      Set.mem_insert_of_mem _ (by simpa [Metric.mem_closedBall] using hd)⟩
  by_cases hF : (hA.toFinset).Nonempty
  · obtain ⟨γ₀, hγ₀F, hmin⟩ := (hA.toFinset).exists_min_image (fun γ => dist (γ * x) y) hF
    have hγ₀ : γ₀ ∈ latticeSubgroup ∧ dist (γ₀ * x) y ≤ 1 := by
      simpa using (Set.Finite.mem_toFinset hA).mp hγ₀F
    have hpos : 0 < dist (γ₀ * x) y := dist_pos.mpr (hne γ₀ hγ₀.1)
    refine ⟨min 1 (dist (γ₀ * x) y), lt_min one_pos hpos, fun γ hγ => ?_⟩
    by_cases hd : dist (γ * x) y ≤ 1
    · exact le_trans (min_le_right _ _) (hmin γ ((Set.Finite.mem_toFinset hA).mpr ⟨hγ, hd⟩))
    · exact le_trans (min_le_left _ _) (le_of_lt (not_le.mp hd))
  · refine ⟨1, one_pos, fun γ hγ => ?_⟩
    by_contra hlt
    exact hF ⟨γ, (Set.Finite.mem_toFinset hA).mpr ⟨hγ, le_of_lt (not_le.mp hlt)⟩⟩

