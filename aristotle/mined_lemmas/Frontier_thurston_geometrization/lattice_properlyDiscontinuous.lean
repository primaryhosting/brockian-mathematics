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

theorem lattice_properlyDiscontinuous (K : Set Euc3) (hK : IsCompact K) :
    {γ : Euc3 | γ ∈ latticeSubgroup ∧ ∃ x ∈ K, γ * x ∈ K}.Finite := by
  have hK' : IsCompact (K : Set (ℝ × ℝ × ℝ)) := hK
  obtain ⟨R, hR⟩ := hK'.isBounded.subset_closedBall (0 : ℝ × ℝ × ℝ)
  set N : ℤ := ⌈2 * R⌉ with hN
  have hfin : (Set.Icc (-N) N ×ˢ (Set.Icc (-N) N ×ˢ Set.Icc (-N) N)).Finite :=
    (Set.finite_Icc _ _).prod ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _))
  have hbound : ∀ y ∈ K, |(y : ℝ × ℝ × ℝ).1| ≤ R ∧ |(y : ℝ × ℝ × ℝ).2.1| ≤ R ∧
      |(y : ℝ × ℝ × ℝ).2.2| ≤ R := by
    intro y hy
    have h := Metric.mem_closedBall.mp (hR hy)
    rw [Prod.dist_eq, max_le_iff] at h
    obtain ⟨h1, h2⟩ := h
    rw [Prod.dist_eq, max_le_iff] at h2
    refine ⟨?_, ?_, ?_⟩
    · simpa [Real.dist_eq] using h1
    · simpa [Real.dist_eq] using h2.1
    · simpa [Real.dist_eq] using h2.2
  apply Set.Finite.subset
    (hfin.image (fun v : ℤ × ℤ × ℤ => (((v.1 : ℝ), (v.2.1 : ℝ), (v.2.2 : ℝ)) : Euc3)))
  rintro γ ⟨hγ, x, hx, hγx⟩
  obtain ⟨v, rfl⟩ := hγ
  obtain ⟨hx1, hx2, hx3⟩ := hbound x hx
  obtain ⟨hy1, hy2, hy3⟩ := hbound _ hγx
  have hNR : 2 * R ≤ (N : ℝ) := Int.le_ceil _
  have key : ∀ (m : ℤ) (s t : ℝ), |s| ≤ R → |t| ≤ R → (m : ℝ) + s = t → m ∈ Set.Icc (-N) N := by
    intro m s t hs ht hst
    have h1 : |(m : ℝ)| ≤ (N : ℝ) := by
      rw [abs_le] at hs ht ⊢
      constructor <;> [linarith [hs.1, ht.2]; linarith [hs.2, ht.1]]
    have h2 : |m| ≤ N := by exact_mod_cast (by rwa [← Int.cast_abs] at h1 : ((|m| : ℤ) : ℝ) ≤ (N : ℝ))
    exact Set.mem_Icc.mpr (abs_le.mp h2)
  refine ⟨v, ⟨?_, ?_, ?_⟩, rfl⟩
  · exact key v.1 x.1 _ hx1 hy1 rfl
  · exact key v.2.1 x.2.1 _ hx2 hy2 rfl
  · exact key v.2.2 x.2.2 _ hx3 hy3 rfl

/-- The flat 3-torus `ℝ³ / ℤ³`. -/
