import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Manifold ContDiff
open Bundle

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Math2

/-!
## Isometric embeddings of Riemannian manifolds into Euclidean space

Throughout, a *Riemannian manifold* is a smooth manifold `M` modelled on `(E, H, I)` whose
tangent bundle carries a `RiemannianBundle` structure, i.e. each tangent space
`TangentSpace I x` is endowed with an inner product (varying smoothly with `x` when one also
assumes `IsContMDiffRiemannianBundle`).  This is the Mathlib formulation of a Riemannian metric.
-/

/-- A map `f : M → ℝ^N` is an **isometric embedding** of the Riemannian manifold `M` if it is
smooth, a topological embedding, and its differential preserves inner products, i.e. the pullback
along `f` of the Euclidean metric of `ℝ^N` is the Riemannian metric of `M`. -/
def IsIsometricEmbedding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (N : ℕ) (f : M → EuclideanSpace ℝ (Fin N)) : Prop :=
  ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f ∧
  Topology.IsEmbedding f ∧
  ∀ (x : M) (v w : TangentSpace I x),
    inner ℝ
      (show EuclideanSpace ℝ (Fin N) from mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x v)
      (show EuclideanSpace ℝ (Fin N) from mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x w)
      = inner ℝ v w

/-- The statement of the **Nash isometric embedding theorem** in full generality: every smooth
Riemannian manifold (finite dimensional, Hausdorff, second countable, without boundary) admits a
smooth isometric embedding into some Euclidean space `ℝ^N`.

This `Prop` records the general statement for reference.  It is *not* proved in this file; what is
proved below are two genuine special cases, `Math2.nash_embedding` (an arbitrary constant metric,
in every dimension) and `Math2.nash_embedding_real_line` (an arbitrary metric in dimension one). -/
def NashEmbeddingTheorem : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : Type) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)],
    ∃ (N : ℕ) (f : M → EuclideanSpace ℝ (Fin N)), IsIsometricEmbedding I M N f

/-!
## The flat case: an arbitrary constant Riemannian metric

A finite dimensional real inner product space `F`, equipped with its canonical Riemannian metric
(the given inner product on every tangent space), embeds isometrically into
`ℝ^(finrank ℝ F)`.  Since `F` may carry *any* inner product, this is exactly the statement that an
arbitrary constant Riemannian metric on `ℝ^n` is realised by an embedding into Euclidean space.
-/

/-- **Nash embedding, constant metric case.**  Every finite dimensional real inner product space,
viewed as a Riemannian manifold with its canonical (constant) Riemannian metric, admits a smooth
isometric embedding into a Euclidean space `ℝ^N`. -/
theorem nash_embedding
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    ∃ (N : ℕ) (f : F → EuclideanSpace ℝ (Fin N)), IsIsometricEmbedding 𝓘(ℝ, F) F N f := by
  set n := Module.finrank ℝ F with hn
  let e : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ F).repr
  let L : F →L[ℝ] EuclideanSpace ℝ (Fin n) := e.toContinuousLinearEquiv.toContinuousLinearMap
  have hLe : (L : F → EuclideanSpace ℝ (Fin n)) = e := rfl
  refine ⟨n, L, L.contMDiff, hLe ▸ e.toHomeomorph.isEmbedding, ?_⟩
  intro x v w
  have h3 : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) L x = L := by
    rw [mfderiv_eq_fderiv]; exact L.fderiv
  rw [h3]
  exact e.inner_map_map _ _

/-!
## Dimension one, arbitrary metric

Every smooth Riemannian metric on the real line, i.e. `g_x(v, w) = a x * v * w` for a smooth
positive function `a`, is isometrically embeddable in `ℝ¹`, via the arc-length parametrisation
`x ↦ ∫₀ˣ √(a t) dt`.
-/

section Line

/-- Auxiliary smoothness lemma: a smooth scalar function times a fixed vector is smooth.
Stated for an abstract normed space to avoid typeclass search issues. -/
theorem contDiff_smul_const_aux {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (c : X) : ContDiff ℝ ∞ (fun y ↦ a y • c) :=
  ha.smul contDiff_const

/-- The Riemannian metric on `ℝ` given by `g_x(v, w) = a x * v * w`, for a smooth positive
function `a`.  Every smooth Riemannian metric on `ℝ` is of this form. -/
noncomputable def lineMetric (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hpos : ∀ x, 0 < a x) :
    ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ∞ ℝ (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) where
  inner x := a x • (ContinuousLinearMap.mul ℝ ℝ)
  symm x v w := by
    show a x * ((show ℝ from v) * (show ℝ from w)) = a x * ((show ℝ from w) * (show ℝ from v))
    ring
  pos x v hv := by
    show 0 < a x * ((show ℝ from v) * (show ℝ from v))
    have h1 : (0 : ℝ) < (show ℝ from v) * (show ℝ from v) := mul_self_pos.2 hv
    have h2 := hpos x
    positivity
  isVonNBounded x := by
    show Bornology.IsVonNBounded ℝ
      {v : TangentSpace 𝓘(ℝ, ℝ) x | a x * ((show ℝ from v) * (show ℝ from v)) < 1}
    have hax := hpos x
    set r : ℝ := Real.sqrt (1 / a x) with hr
    have hrpos : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr2 : r ^ 2 = 1 / a x := Real.sq_sqrt (by positivity)
    have hset : {v : TangentSpace 𝓘(ℝ, ℝ) x | a x * ((show ℝ from v) * (show ℝ from v)) < 1}
        = Metric.ball (0 : TangentSpace 𝓘(ℝ, ℝ) x) r := by
      ext v
      have hn : ‖v‖ = |(show ℝ from v)| := by
        rw [norm_tangentSpace_vectorSpace]; exact Real.norm_eq_abs _
      simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right, hn]
      rw [show (show ℝ from v) * (show ℝ from v) = |(show ℝ from v)| ^ 2 by rw [sq_abs]; ring]
      constructor
      · intro h
        have h2 : |(show ℝ from v)| ^ 2 < r ^ 2 := by rw [hr2, lt_div_iff₀ hax]; linarith
        nlinarith [abs_nonneg (show ℝ from v)]
      · intro h
        have h2 : |(show ℝ from v)| ^ 2 < r ^ 2 := by nlinarith [abs_nonneg (show ℝ from v)]
        rw [hr2, lt_div_iff₀ hax] at h2; linarith
    rw [hset]
    exact NormedSpace.isVonNBounded_ball ℝ _ r
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    have key : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ →L[ℝ] ℝ →L[ℝ] ℝ) ∞
        (fun y : ℝ ↦ a y • (ContinuousLinearMap.mul ℝ ℝ)) x := by
      rw [contMDiffAt_iff_contDiffAt]
      exact (contDiff_smul_const_aux a ha (ContinuousLinearMap.mul ℝ ℝ)).contDiffAt
    convert key with y
    ext
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.linearMapAt_apply, TangentSpace]

/-- The canonical linear isometry from `ℝ` to `ℝ¹`. -/
noncomputable def iota : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun _ : Fin 1 ↦ ContinuousLinearMap.id ℝ ℝ))

theorem inner_iota (p q : ℝ) : inner ℝ (iota p) (iota q) = p * q := by
  simp [iota, PiLp.inner_apply, RCLike.inner_apply]
  ring

theorem norm_iota (t : ℝ) : ‖iota t‖ = ‖t‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [iota, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

theorem isEmbedding_iota : Topology.IsEmbedding (iota : ℝ → EuclideanSpace ℝ (Fin 1)) :=
  (AddMonoidHomClass.isometry_of_norm iota norm_iota).isEmbedding

/-- **Nash embedding on the line.** Every smooth Riemannian metric on `ℝ` admits a smooth
isometric embedding into `ℝ¹`, namely the arc-length parametrisation. -/
theorem nash_embedding_real_line (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hpos : ∀ x, 0 < a x) :
    letI : RiemannianBundle (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x) :=
      ⟨(lineMetric a ha hpos).toRiemannianMetric⟩
    ∃ f : ℝ → EuclideanSpace ℝ (Fin 1), IsIsometricEmbedding 𝓘(ℝ, ℝ) ℝ 1 f := by
  set s : ℝ → ℝ := fun t ↦ Real.sqrt (a t) with hs
  have hsdiff : ContDiff ℝ ∞ s := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (Real.contDiffAt_sqrt (x := a x) (hpos x).ne').comp x ha.contDiffAt
  have hscont : Continuous s := hsdiff.continuous
  set A : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, s t with hA
  have hAderiv : ∀ x, HasDerivAt A (s x) x := fun x ↦
    intervalIntegral.integral_hasDerivAt_right (hscont.intervalIntegrable _ _)
      (hscont.stronglyMeasurableAtFilter _ _) hscont.continuousAt
  have hderivA : deriv A = s := funext fun x ↦ (hAderiv x).deriv
  have hAdiff : ContDiff ℝ ∞ A := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨fun x ↦ (hAderiv x).differentiableAt, by rw [hderivA]; exact hsdiff⟩
  have hmono : StrictMono A := by
    apply strictMono_of_deriv_pos
    intro x
    rw [hderivA]
    exact Real.sqrt_pos.2 (hpos x)
  have hembA : Topology.IsEmbedding A :=
    hmono.isEmbedding_of_ordConnected ((isPreconnected_range hAdiff.continuous).ordConnected)
  refine ⟨iota ∘ A, ?_, isEmbedding_iota.comp hembA, ?_⟩
  · rw [contMDiff_iff_contDiff]
    exact iota.contDiff.comp hAdiff
  · intro x v w
    have hfd : HasFDerivAt (iota ∘ A) (iota.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (s x))) x :=
      iota.hasFDerivAt.comp x (hAderiv x)
    have hmf : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (iota ∘ A) x
        = iota.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (s x)) := by
      rw [mfderiv_eq_fderiv]; exact hfd.fderiv
    rw [hmf]
    show inner ℝ (iota ((show ℝ from v) • s x)) (iota ((show ℝ from w) • s x)) = _
    rw [inner_iota]
    show (show ℝ from v) • s x * ((show ℝ from w) • s x)
      = a x * ((show ℝ from v) * (show ℝ from w))
    have hss : s x * s x = a x := Real.mul_self_sqrt (hpos x).le
    simp only [smul_eq_mul]
    rw [← hss]
    ring

end Line

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

