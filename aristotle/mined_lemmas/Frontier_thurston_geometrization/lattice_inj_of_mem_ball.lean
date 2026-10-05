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

lemma lattice_inj_of_mem_ball (c x y : Euc3) (hx : x ∈ Metric.ball c (1/2))
    (hy : y ∈ Metric.ball c (1/2)) (hxy : torusProj x = torusProj y) : x = y := by
  obtain ⟨γ, hγ, hgxy⟩ := exists_lattice_of_torusProj_eq hxy
  obtain ⟨v, rfl⟩ := hγ
  obtain ⟨hx1, hx2, hx3⟩ := Euc3.abs_sub_lt_of_mem_ball hx
  obtain ⟨hy1, hy2, hy3⟩ := Euc3.abs_sub_lt_of_mem_ball hy
  have hco : ((v.1 : ℝ) + x.1, (v.2.1 : ℝ) + x.2.1, (v.2.2 : ℝ) + x.2.2) = (y.1, y.2.1, y.2.2) :=
    hgxy
  rw [Prod.mk.injEq, Prod.mk.injEq] at hco
  obtain ⟨e1, e2, e3⟩ := hco
  have key : ∀ (m : ℤ) (a b ca : ℝ), |a - ca| < 1/2 → |b - ca| < 1/2 →
      (m : ℝ) + a = b → m = 0 := by
    intro m a b ca ha hb hab
    have h1 : |(m : ℝ)| < 1 := by
      rw [abs_lt] at ha hb ⊢
      constructor <;> [linarith [ha.1, hb.2]; linarith [ha.2, hb.1]]
    have h2 : |m| < 1 := by
      exact_mod_cast (by rwa [← Int.cast_abs] at h1 : ((|m| : ℤ) : ℝ) < 1)
    have h3 := abs_lt.mp h2
    omega
  have h1 : v.1 = 0 := key v.1 x.1 y.1 c.1 hx1 hy1 e1
  have h2 : v.2.1 = 0 := key v.2.1 x.2.1 y.2.1 c.2.1 hx2 hy2 e2
  have h3 : v.2.2 = 0 := key v.2.2 x.2.2 y.2.2 c.2.2 hx3 hy3 e3
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rw [← e1, h1]; simp
  · rw [← e2, h2]; simp
  · rw [← e3, h3]; simp

/-- Every open ball in `ℝ³` is homeomorphic to `ℝ³`. -/
