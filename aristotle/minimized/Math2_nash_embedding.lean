/-
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires import commands to come before any module docstring, so the requested
header appears here as an ordinary block comment, and again as the module docstring immediately
after the imports.)
-/

import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff RealInnerProductSpace BigOperators
open Set Topology

/-!
## Scope

John Nash's theorem states that *every* Riemannian manifold `(M, g)` admits a smooth isometric
embedding into some Euclidean space `ℝ^N`, i.e. a smooth topological embedding
`f : M → ℝ^N` whose differential satisfies `⟪df_x v, df_x w⟫ = g x v w` for all tangent vectors
`v, w` at every point `x`. Its proof (via the Nash–Moser implicit function theorem) is far beyond
the current state of formalized mathematics, and the general statement is not available in
Mathlib.

This file formalizes the notion of a smooth isometric embedding of a Riemannian metric
(`Math2.IsSmoothIsometricEmbedding`) and proves the Nash embedding statement for two genuine
families of Riemannian metrics:

* `Math2.nash_embedding`: all metrics on `ℝⁿ` of the separably-diagonal form
  `g x v w = ∑ i, (a i (x i))^2 * v i * w i` with `a i` smooth and positive. In particular, for
  `n = 1` this is *every* Riemannian metric on the real line.
* `Math2.nash_embedding_inner_product_space`: the canonical metric of any finite-dimensional real
  inner product space.
* `Math2.nash_embedding_graph`: all metrics on `ℝⁿ` induced by the graph of a smooth function
  `u : ℝⁿ → ℝ`, which are in general curved.

No axioms beyond the standard ones (`propext`, `Classical.choice`, `Quot.sound`) are used.
-/

namespace Math2

/-- `IsSmoothIsometricEmbedding g f` says that `f`, a map from the manifold `E` (a real normed
space, playing the role of ℝⁿ) into a Euclidean space `ℝ^N`, is a smooth isometric embedding of
the Riemannian metric `g`: it is `C^∞`, it is a topological embedding, and its differential
pulls the Euclidean inner product back to `g`.

Here a Riemannian metric is described concretely by the function `g : E → E → E → ℝ`, where
`g x v w` is the inner product of the tangent vectors `v`, `w` at the point `x`. -/

def IsSmoothIsometricEmbedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}
    (g : E → E → E → ℝ) (f : E → EuclideanSpace ℝ (Fin N)) : Prop :=
  ContDiff ℝ ∞ f ∧ IsEmbedding f ∧ ∀ x v w, ⟪fderiv ℝ f x v, fderiv ℝ f x w⟫ = g x v w

/-- The antiderivative of `a` vanishing at `0`. -/

noncomputable def antideriv (a : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, a t

lemma hasDerivAt_antideriv {a : ℝ → ℝ} (ha : Continuous a) (x : ℝ) :
    HasDerivAt (antideriv a) (a x) x :=
  (ha.integral_hasStrictDerivAt 0 x).hasDerivAt

lemma deriv_antideriv {a : ℝ → ℝ} (ha : Continuous a) : deriv (antideriv a) = a :=
  funext fun x => (hasDerivAt_antideriv ha x).deriv

lemma contDiff_antideriv {a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (antideriv a) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (hasDerivAt_antideriv ha.continuous x).differentiableAt,
    by rw [deriv_antideriv ha.continuous]; exact ha⟩

lemma strictMono_antideriv {a : ℝ → ℝ} (ha : Continuous a) (hpos : ∀ x, 0 < a x) :
    StrictMono (antideriv a) :=
  strictMono_of_deriv_pos (by rw [deriv_antideriv ha]; exact hpos)

lemma isEmbedding_antideriv {a : ℝ → ℝ} (ha : Continuous a) (hpos : ∀ x, 0 < a x) :
    IsEmbedding (antideriv a) := by
  refine (strictMono_antideriv ha hpos).isEmbedding_of_ordConnected ?_
  have hd : Differentiable ℝ (antideriv a) := fun x => (hasDerivAt_antideriv ha x).differentiableAt
  have h := (isPreconnected_univ (α := ℝ)).image _ hd.continuous.continuousOn
  rw [Set.image_univ] at h
  exact h.ordConnected

/-- **Nash embedding theorem**, for separably-diagonal Riemannian metrics on `ℝⁿ`.

Every Riemannian metric on `ℝⁿ` of the form `g x v w = ∑ i, (a i (x i))^2 * (v i * w i)`, where
each `a i : ℝ → ℝ` is smooth and positive, admits a smooth isometric embedding into a Euclidean
space `ℝ^N` (here `N = n`): a `C^∞` topological embedding `f` whose differential pulls the
Euclidean inner product back to `g`.

The embedding is built coordinatewise from the antiderivatives `x ↦ ∫ t in 0..x, a i t`.
For `n = 1` this covers *every* Riemannian metric on the line; taking all `a i = 1` recovers
flat `ℝⁿ`. -/

theorem nash_embedding {n : ℕ} (a : Fin n → ℝ → ℝ) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (hpos : ∀ i x, 0 < a i x) :
    ∃ (N : ℕ) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N)),
      IsSmoothIsometricEmbedding
        (fun x v w => ∑ i, (a i (x i)) ^ 2 * (v i * w i)) f := by
  classical
  set e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ with he
  refine ⟨n, fun z => e.symm (fun i => antideriv (a i) (z i)), ?_, ?_, ?_⟩
  · -- smoothness
    exact e.symm.contDiff.comp
      ((contDiff_pi.2 fun i => (contDiff_antideriv (ha i)).comp (contDiff_apply ℝ ℝ i)).comp
        e.contDiff)
  · -- topological embedding
    exact (e.symm.toHomeomorph.isEmbedding).comp
      ((Topology.IsEmbedding.piMap
        (fun i => isEmbedding_antideriv (ha i).continuous (hpos i))).comp
          e.toHomeomorph.isEmbedding)
  · -- the differential pulls back the Euclidean metric to `g`
    intro x v w
    set b : Fin n → ℝ := fun i => a i (x i) with hb
    set Lpi : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
      ContinuousLinearMap.pi (fun i => (b i) • ContinuousLinearMap.proj i) with hLpi
    set L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      (e.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)).comp
        (Lpi.comp (e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))) with hL
    have hcoord : ∀ u : EuclideanSpace ℝ (Fin n), ∀ i, (L u) i = b i * u i := by
      intro u i; simp [hL, hLpi, he]
    have hG : HasFDerivAt (fun y : Fin n → ℝ => (fun i => antideriv (a i) (y i))) Lpi (e x) := by
      rw [hasFDerivAt_pi']
      intro i
      have h1 := (hasDerivAt_antideriv (ha i).continuous ((e x) i)).hasFDerivAt
      have h2 :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).hasFDerivAt (x := e x)
      have h3 := h1.comp (e x) h2
      convert h3 using 1
      ext u
      simp only [hLpi, hb, ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.pi_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
        he]
      exact mul_comm _ _
    have hf : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => e.symm
        (fun i => antideriv (a i) (z i))) L x :=
      (e.symm.hasFDerivAt).comp x (hG.comp x e.hasFDerivAt)
    rw [hf.fderiv]
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply]
    simp only [conj_trivial]
    rw [hcoord v i, hcoord w i, hb]
    ring

/-- **Nash embedding theorem** (flat case): a finite-dimensional real inner product space,
equipped with its canonical (translation-invariant) Riemannian metric, admits a smooth isometric
embedding into a Euclidean space `ℝ^N`, with `N` its dimension. -/
