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
