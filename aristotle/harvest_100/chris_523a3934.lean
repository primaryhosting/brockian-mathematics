/-
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Nash's isometric embedding theorem states that every Riemannian manifold `(M, g)` admits a
smooth isometric embedding into some Euclidean space `ℝ^N`, where *isometric* means that the
pullback of the Euclidean metric along the embedding is `g`, i.e.
`⟪Df(x) u, Df(x) v⟫ = g x (u, v)` for all tangent vectors `u, v`.

This file formalizes the theorem in the following cases, stated in the concrete (chart-level)
form of the pullback identity above.

* `Math2.nash_embedding` : the **one-dimensional** case. Every smooth Riemannian metric on the
  line (a smooth positive function `g : ℝ → ℝ`, the metric being `(u, v) ↦ g x * (u * v)`)
  admits a smooth isometric embedding into `ℝ^N` (with `N = 1`), given by the arclength
  function `x ↦ ∫_0^x √(g t) dt`.
* `Math2.nash_embedding_separable` : the case of a **separable diagonal** metric in arbitrary
  dimension `n`, i.e. `g x (u, v) = ∑ i, aᵢ (xᵢ) * uᵢ * vᵢ` with each `aᵢ` smooth and positive.
  The embedding into `ℝ^n` is obtained by applying the one-dimensional construction in each
  coordinate.
* `Math2.nash_embedding_const` : the case of a **constant** metric in arbitrary dimension `n`,
  given by a positive definite matrix `G`; the embedding into `ℝ^n` is the linear map with
  matrix a square root `B` of `G` (`Bᵀ * B = G`).

The general case (arbitrary dimension, arbitrary smooth metric) is *not* formalized here.
-/

open Topology Matrix
open scoped ContDiff MatrixOrder

namespace Math2

/-- The canonical linear isometry from `ℝ` onto the one-dimensional Euclidean space
`EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def lineToEuclidean : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun a := EuclideanSpace.single 0 a
  map_add' a b := by ext i; simp [EuclideanSpace.single_apply]; split <;> simp
  map_smul' c a := by ext i; simp [EuclideanSpace.single_apply]
  norm_map' a := by simp

/-- The arclength function of a smooth positive metric `g` on the line: a smooth embedding
`F : ℝ → ℝ` with `F' x = √(g x)`, namely `F x = ∫_0^x √(g t) dt`. -/
theorem exists_arclength (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ IsEmbedding F ∧
      ∀ x, HasDerivAt F (Real.sqrt (g x)) x := by
  set s : ℝ → ℝ := fun t => Real.sqrt (g t)
  have hs_smooth : ContDiff ℝ ∞ s := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (Real.contDiffAt_sqrt (ne_of_gt (hpos x))).comp x hg.contDiffAt
  have hs_pos : ∀ x, 0 < s x := fun x => Real.sqrt_pos.2 (hpos x)
  set F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, s t
  have hF : ∀ x, HasDerivAt F (s x) x := fun x =>
    (hs_smooth.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hderiv : deriv F = s := funext fun x => (hF x).deriv
  have hFsmooth : ContDiff ℝ ∞ F :=
    contDiff_infty_iff_deriv.2 ⟨fun x => (hF x).differentiableAt, by rw [hderiv]; exact hs_smooth⟩
  have hmono : StrictMono F := strictMono_of_deriv_pos (by rw [hderiv]; exact hs_pos)
  exact ⟨F, hFsmooth, hmono.isEmbedding_of_ordConnected
    (by simpa using (isPreconnected_univ.image F hFsmooth.continuous.continuousOn).ordConnected),
    hF⟩

/-- **Nash isometric embedding theorem, one-dimensional case.**

A Riemannian metric on the line is a smooth positive function `g`, the associated inner product
on the tangent line at `x` being `(u, v) ↦ g x * (u * v)`.  Then there is a Euclidean space
`ℝ^N` and a smooth embedding `f : ℝ → ℝ^N` which is isometric, in the sense that the pullback
along `f` of the Euclidean inner product is the given metric:
`⟪Df(x) u, Df(x) v⟫ = g x * (u * v)`.

The embedding is the arclength parametrization `x ↦ ∫_0^x √(g t) dt`, viewed inside `ℝ^1`. -/
theorem nash_embedding (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) :
    ∃ (N : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ∞ f ∧ IsEmbedding f ∧
      ∀ x u v : ℝ, inner ℝ (fderiv ℝ f x u) (fderiv ℝ f x v) = g x * (u * v) := by
  obtain ⟨F, hFsmooth, hemb, hF⟩ := exists_arclength g hg hpos
  have hs_sq : ∀ x, Real.sqrt (g x) * Real.sqrt (g x) = g x := fun x =>
    Real.mul_self_sqrt (hpos x).le
  refine ⟨1, fun x => lineToEuclidean (F x), lineToEuclidean.contDiff.comp hFsmooth,
    lineToEuclidean.isometry.isEmbedding.comp hemb, ?_⟩
  intro x u v
  have hfd : HasFDerivAt (fun x => lineToEuclidean (F x))
      (lineToEuclidean.toContinuousLinearMap.comp
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Real.sqrt (g x)))) x :=
    (lineToEuclidean.toContinuousLinearMap.hasFDerivAt).comp x (hF x).hasFDerivAt
  rw [hfd.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
  rw [LinearIsometry.coe_toContinuousLinearMap, lineToEuclidean.inner_map_map]
  simp only [RCLike.inner_apply, conj_trivial]
  linear_combination (u * v) * hs_sq x

/-- **Nash isometric embedding theorem, separable diagonal metrics in arbitrary dimension.**

Let `a i : ℝ → ℝ` be smooth and positive for `i = 1, …, n`, and consider on `ℝ^n` the
Riemannian metric `g x (u, v) = ∑ i, a i (xᵢ) * (uᵢ * vᵢ)`.  Then there is a Euclidean space
`ℝ^N` and a smooth embedding `f : ℝ^n → ℝ^N` which is isometric, in the sense that the pullback
along `f` of the Euclidean inner product is the given metric.

The embedding is obtained by applying the one-dimensional arclength construction in each
coordinate separately. -/
theorem nash_embedding_separable {n : ℕ} (a : Fin n → ℝ → ℝ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (hpos : ∀ i x, 0 < a i x) :
    ∃ (N : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ∞ f ∧ IsEmbedding f ∧
      ∀ x u v : EuclideanSpace ℝ (Fin n),
        inner ℝ (fderiv ℝ f x u) (fderiv ℝ f x v)
          = ∑ i, a i (x.ofLp i) * (u.ofLp i * v.ofLp i) := by
  choose F hFsmooth hFemb hFderiv using fun i => exists_arclength (a i) (ha i) (hpos i)
  set E := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ) with hE
  set Ec : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
    (E : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)) with hEc
  set Es : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (E.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) with hEs
  refine ⟨n, fun x => Es (Pi.map F (Ec x)), ?_, ?_, ?_⟩
  · exact Es.contDiff.comp
      ((contDiff_pi.2 fun i => (hFsmooth i).comp (contDiff_apply ℝ ℝ i)).comp Ec.contDiff)
  · exact E.symm.toHomeomorph.isEmbedding.comp
      ((Topology.IsEmbedding.piMap hFemb).comp E.toHomeomorph.isEmbedding)
  · intro x u v
    have hpi : HasFDerivAt (fun y : Fin n → ℝ => Pi.map F y)
        (ContinuousLinearMap.pi fun i =>
          (Real.sqrt (a i ((Ec x) i))) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i)
        (Ec x) :=
      hasFDerivAt_pi'' (fun i => (hFderiv i ((Ec x) i)).comp_hasFDerivAt (Ec x)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt)
    have hfd : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => Es (Pi.map F (Ec z)))
        (Es.comp ((ContinuousLinearMap.pi fun i =>
          (Real.sqrt (a i ((Ec x) i))) •
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).comp Ec)) x := by
      simpa [Function.comp_def] using Es.hasFDerivAt.comp x (hpi.comp x Ec.hasFDerivAt)
    rw [hfd.fderiv]
    simp [PiLp.inner_apply, RCLike.inner_apply, hEs, hEc, hE]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := Real.mul_self_sqrt (hpos i (x.ofLp i)).le
    linear_combination (u.ofLp i * v.ofLp i) * h

/-- **Nash isometric embedding theorem, constant metric in arbitrary dimension.**

A constant Riemannian metric on `ℝ^n` is given by a positive definite matrix `G`, the inner
product of two tangent vectors `u, v` being `uᵀ G v`.  Then there is a Euclidean space `ℝ^N`
and a smooth embedding `f : ℝ^n → ℝ^N` which is isometric, in the sense that the pullback along
`f` of the Euclidean inner product is the given metric:
`⟪Df(x) u, Df(x) v⟫ = uᵀ G v`.

The embedding is the linear map given by a matrix square root of `G`. -/
theorem nash_embedding_const {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    ∃ (N : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)),
      ContDiff ℝ ∞ f ∧ IsEmbedding f ∧
      ∀ x u v : EuclideanSpace ℝ (Fin n),
        inner ℝ (fderiv ℝ f x u) (fderiv ℝ f x v) = u.ofLp ⬝ᵥ G.mulVec v.ofLp := by
  obtain ⟨B, -, hB⟩ :=
    CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1
      (Matrix.isStrictlyPositive_iff_posDef.2 hG)
  have hBt : star B = Bᵀ := rfl
  rw [hBt] at hB
  -- the linear map with matrix `B`
  set T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin B
    with hT_def
  have key : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (T u) (T v) = u.ofLp ⬝ᵥ G.mulVec v.ofLp := by
    intro u v
    rw [hB, hT_def]
    simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.vecMul_transpose]
    rw [← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, dotProduct_comm]
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have h0 : u.ofLp ⬝ᵥ G.mulVec u.ofLp = 0 := by rw [← key u u, hu]; simp
    by_contra hne
    have hu0 : u.ofLp ≠ 0 := fun h => hne (by ext i; simpa using congrFun h i)
    have hpos := hG.dotProduct_mulVec_pos hu0
    rw [show star u.ofLp = u.ofLp from by ext i; simp] at hpos
    exact absurd h0 (ne_of_gt hpos)
  refine ⟨n, T, ?_, ?_, ?_⟩
  · exact (T.toContinuousLinearMap : _ →L[ℝ] _).contDiff
  · exact (LinearMap.isClosedEmbedding_of_injective
      (f := T) (LinearMap.ker_eq_bot.2 hinj)).isEmbedding
  · intro x u v
    have hfd : fderiv ℝ (fun y => T y) x = (T.toContinuousLinearMap : _ →L[ℝ] _) :=
      (T.toContinuousLinearMap : _ →L[ℝ] _).hasFDerivAt.fderiv
    rw [show (fun y => T y) = (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) from rfl]
      at hfd
    rw [hfd]
    simpa using key u v

end Math2

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

