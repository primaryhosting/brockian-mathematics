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

lemma exists_lattice_translate (x : Euc3) : ∃ γ ∈ latticeSubgroup, γ * x ∈ cube := by
  have key : ∀ a : ℝ, |(-(⌊a⌋ : ℝ)) + a| ≤ 2 := by
    intro a
    have h0 : (0 : ℝ) ≤ Int.fract a := Int.fract_nonneg a
    have h1 : Int.fract a < 1 := Int.fract_lt_one a
    have h2 : (-(⌊a⌋ : ℝ)) + a = Int.fract a := by rw [Int.fract]; ring
    rw [h2, abs_of_nonneg h0]
    linarith
  refine ⟨Euc3.mk (-(⌊x.1⌋ : ℝ)) (-(⌊x.2.1⌋ : ℝ)) (-(⌊x.2.2⌋ : ℝ)),
    ⟨(-⌊x.1⌋, -⌊x.2.1⌋, -⌊x.2.2⌋), by simp [Euc3.mk]⟩, ?_⟩
  show (((-(⌊x.1⌋ : ℝ)) + x.1 : ℝ), ((-(⌊x.2.1⌋ : ℝ)) + x.2.1 : ℝ),
      ((-(⌊x.2.2⌋ : ℝ)) + x.2.2 : ℝ)) ∈ Metric.closedBall (0 : ℝ × ℝ × ℝ) 2
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Prod.dist_eq, max_le_iff]
  refine ⟨?_, ?_, ?_⟩ <;> simpa [Real.dist_eq] using key _

instance : CompactSpace FlatThreeTorus := by
  constructor
  have himg : (Set.univ : Set FlatThreeTorus) = torusProj '' cube := by
    refine Set.eq_of_subset_of_subset ?_ (fun _ _ => Set.mem_univ _)
    rintro y -
    obtain ⟨x, rfl⟩ := torusProj_surjective y
    obtain ⟨γ, hγ, hmem⟩ := exists_lattice_translate x
    exact ⟨γ * x, hmem, torusProj_mul hγ x⟩
  rw [himg]
  exact isCompact_cube.image continuous_torusProj

/-! ### The flat 3-torus is a closed 3-manifold -/

