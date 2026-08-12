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

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The complex Hilbert space `L²(E)` of square integrable functions on a finite-dimensional
real inner product space `E`, with respect to the Lebesgue (Haar) measure. -/
abbrev L2Space (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] : Type _ := ↥(Lp (α := E) ℂ 2 volume)

/-- Schwartz functions viewed as elements of `L²(E)`. -/
def toL2 : 𝓢(E, ℂ) →L[ℂ] L2Space E := SchwartzMap.toLpCLM ℂ ℂ 2 volume

theorem toL2_apply (f : 𝓢(E, ℂ)) : toL2 f = f.toLp 2 volume := rfl

theorem injective_toL2 : Function.Injective (toL2 (E := E)) := SchwartzMap.injective_toLp 2 volume

theorem denseRange_toL2 : DenseRange (toL2 (E := E)) :=
  SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top

/-- The *free Laplacian* `-Δ`, as an unbounded operator on `L²(E)` whose domain is the space of
Schwartz functions. -/
def freeLaplacian : L2Space E →ₗ.[ℂ] L2Space E where
  domain := LinearMap.range (toL2 (E := E)).toLinearMap
  toFun := ((toL2 (E := E)).toLinearMap ∘ₗ (-(laplacianCLM ℂ E 𝓢(E, ℂ))).toLinearMap) ∘ₗ
    (LinearEquiv.ofInjective (toL2 (E := E)).toLinearMap injective_toL2).symm.toLinearMap

theorem freeLaplacian_domain :
    (freeLaplacian (E := E)).domain = LinearMap.range (toL2 (E := E)).toLinearMap := rfl

theorem mem_freeLaplacian_domain (f : 𝓢(E, ℂ)) : toL2 f ∈ (freeLaplacian (E := E)).domain :=
  ⟨f, rfl⟩

theorem freeLaplacian_apply (f : 𝓢(E, ℂ)) (h : toL2 f ∈ (freeLaplacian (E := E)).domain) :
    freeLaplacian ⟨toL2 f, h⟩ = toL2 (-(Δ f)) := by
  show ((toL2 (E := E)).toLinearMap ∘ₗ (-(laplacianCLM ℂ E 𝓢(E, ℂ))).toLinearMap)
      ((LinearEquiv.ofInjective (toL2 (E := E)).toLinearMap injective_toL2).symm
        ⟨toL2 f, h⟩) = _
  have hf : (LinearEquiv.ofInjective (toL2 (E := E)).toLinearMap injective_toL2).symm
      ⟨toL2 f, h⟩ = f := by
    apply (LinearEquiv.ofInjective (toL2 (E := E)).toLinearMap injective_toL2).injective
    simp
    exact Subtype.ext rfl
  rw [hf]
  simp [laplacianCLM_eq]

theorem freeLaplacian_apply' (f : 𝓢(E, ℂ)) (u : (freeLaplacian (E := E)).domain)
    (hu : (u : L2Space E) = toL2 f) : freeLaplacian u = toL2 (-(Δ f)) := by
  have : u = ⟨toL2 f, mem_freeLaplacian_domain f⟩ := Subtype.ext hu
  rw [this, freeLaplacian_apply]

theorem dense_freeLaplacian_domain :
    Dense ((freeLaplacian (E := E)).domain : Set (L2Space E)) := by
  have := denseRange_toL2 (E := E)
  simpa [freeLaplacian_domain, DenseRange, Set.range] using this

/-- An unbounded operator on a complex Hilbert space is *essentially self-adjoint* if it is
densely defined, symmetric, and its adjoint is self-adjoint.  The last condition is the standard
characterisation of essential self-adjointness: it is equivalent to saying that the closure of the
operator is self-adjoint. -/
def IsEssentiallySelfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →ₗ.[ℂ] H) : Prop :=
  Dense (T.domain : Set H) ∧ T.IsFormalAdjoint T ∧ IsSelfAdjoint T.adjoint

/-! ## The Fourier picture -/

/-- The Fourier multiplier of the free Laplacian `-Δ`, namely `ξ ↦ 4π²‖ξ‖²`. -/
def multiplier (ξ : E) : ℝ := 4 * π ^ 2 * ‖ξ‖ ^ 2

/-- `IsFourierMul y w` says that on the Fourier side, `w` is obtained from `y` by multiplying
with the Fourier multiplier `4π²‖ξ‖²` of the free Laplacian. -/
def IsFourierMul (y w : L2Space E) : Prop :=
  (fun ξ => (multiplier ξ : ℂ) * (𝓕 y : L2Space E) ξ) =ᵐ[volume] fun ξ => (𝓕 w : L2Space E) ξ

theorem fourier_lineDeriv_apply (f : 𝓢(E, ℂ)) (m : E) (ξ : E) :
    𝓕 (∂_{m} f) ξ = (2 * π * Complex.I * (inner ℝ ξ m : ℝ)) * 𝓕 f ξ := by
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  have : ((inner ℝ · m) : E → ℝ).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  simp [this]
  ring

/-- The Fourier transform turns `-Δ` into multiplication by `4π²‖ξ‖²`. -/
theorem fourier_laplacian_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (Δ f) ξ = -(multiplier ξ : ℂ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ E with hb
  rw [SchwartzMap.laplacian_eq_sum b f, fourier_sum, SchwartzMap.sum_apply]
  have key : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = (-((inner ℝ ξ (b i) : ℝ)) ^ 2 : ℝ) * ((4 * π ^ 2 : ℝ) * 𝓕 f ξ) := by
    intro i
    rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  simp_rw [key]
  rw [← Finset.sum_mul]
  have hsum : ∑ i, ((-((inner ℝ ξ (b i) : ℝ)) ^ 2 : ℝ) : ℂ) = ((-‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    congr 1
    rw [← b.sum_sq_inner_left ξ, ← Finset.sum_neg_distrib]
  rw [hsum]
  simp only [multiplier]
  push_cast
  ring

theorem fourier_neg_laplacian_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (-(Δ f)) ξ = (multiplier ξ : ℂ) * 𝓕 f ξ := by
  rw [FourierTransform.fourier_neg, SchwartzMap.neg_apply, fourier_laplacian_apply]
  ring

/-- Pairing of an `L²` function against a Schwartz function, as an integral. -/
theorem inner_toL2 (u : L2Space E) (g : 𝓢(E, ℂ)) :
    inner ℂ u (toL2 g) = ∫ ξ, (starRingEnd ℂ) (u ξ) * g ξ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (F := ℂ) g 2 volume] with x hx
  rw [show ((toL2 g : L2Space E) : E → ℂ) x = g x from hx]
  simp [RCLike.inner_apply]
  ring

/-- Pairing an `L²` function with a Schwartz function, computed on the Fourier side. -/
theorem inner_toL2_fourier (u : L2Space E) (g : 𝓢(E, ℂ)) :
    inner ℂ u (toL2 g) = ∫ ξ, (starRingEnd ℂ) ((𝓕 u : L2Space E) ξ) * (𝓕 g) ξ := by
  rw [← MeasureTheory.Lp.inner_fourier_eq u (toL2 g),
    show (𝓕 (toL2 g) : L2Space E) = toL2 (𝓕 g) from SchwartzMap.toLp_fourier_eq g]
  exact inner_toL2 _ _

/-- Local integrability is preserved by multiplication with the Fourier multiplier. -/
theorem locallyIntegrable_multiplier_mul {u : E → ℂ} (hu : LocallyIntegrable u volume) :
    LocallyIntegrable (fun ξ => (multiplier ξ : ℂ) * u ξ) volume := by
  rw [locallyIntegrable_iff] at hu ⊢
  intro k hk
  refine MeasureTheory.IntegrableOn.continuousOn_mul ?_ (hu k hk) hk
  refine Continuous.continuousOn ?_
  unfold multiplier
  fun_prop

theorem locallyIntegrable_L2 (u : L2Space E) : LocallyIntegrable (fun ξ => u ξ) volume :=
  (Lp.memLp u).locallyIntegrable (by norm_num)

/-- The key characterisation: the pairing identity defining the adjoint is equivalent to the
multiplication relation on the Fourier side. -/
theorem pairing_iff_isFourierMul (y w : L2Space E) :
    (∀ f : 𝓢(E, ℂ), inner ℂ w (toL2 f) = inner ℂ y (toL2 (-(Δ f)))) ↔ IsFourierMul y w := by
  have hleft : ∀ f : 𝓢(E, ℂ), inner ℂ w (toL2 f)
      = ∫ ξ, (starRingEnd ℂ) ((𝓕 w : L2Space E) ξ) * (𝓕 f) ξ := fun f => inner_toL2_fourier w f
  have hright : ∀ f : 𝓢(E, ℂ), inner ℂ y (toL2 (-(Δ f)))
      = ∫ ξ, (starRingEnd ℂ) ((multiplier ξ : ℂ) * (𝓕 y : L2Space E) ξ) * (𝓕 f) ξ := by
    intro f
    rw [inner_toL2_fourier y (-(Δ f))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [fourier_neg_laplacian_apply, map_mul, Complex.conj_ofReal]
    ring
  constructor
  · intro h
    refine ae_eq_of_integral_contDiff_smul_eq
      (locallyIntegrable_multiplier_mul (locallyIntegrable_L2 (𝓕 y))) (locallyIntegrable_L2 (𝓕 w))
      ?_
    intro g hg hgsupp
    set G : 𝓢(E, ℂ) := (hgsupp.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg) with hG
    have hGval : ∀ ξ, G ξ = (g ξ : ℂ) := fun ξ => rfl
    have hf := h (𝓕⁻ G)
    rw [hleft, hright] at hf
    rw [FourierTransform.fourier_fourierInv_eq G] at hf
    have hf' := congrArg (starRingEnd ℂ) hf
    rw [← integral_conj, ← integral_conj] at hf'
    simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply] at hf'
    calc ∫ ξ, g ξ • ((multiplier ξ : ℂ) * (𝓕 y : L2Space E) ξ)
        = ∫ ξ, ((multiplier ξ : ℂ) * (𝓕 y : L2Space E) ξ) * (starRingEnd ℂ) (G ξ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
          dsimp only
          rw [hGval]
          simp [Complex.conj_ofReal, Complex.real_smul]
          ring
      _ = ∫ ξ, ((𝓕 w : L2Space E) ξ) * (starRingEnd ℂ) (G ξ) := hf'.symm
      _ = ∫ ξ, g ξ • ((𝓕 w : L2Space E) ξ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
          dsimp only
          rw [hGval]
          simp [Complex.conj_ofReal, Complex.real_smul]
          ring
  · intro h f
    rw [hleft, hright]
    refine integral_congr_ae ?_
    filter_upwards [h] with ξ hξ
    rw [hξ]

theorem isFourierMul_toL2 (f : 𝓢(E, ℂ)) : IsFourierMul (toL2 f) (toL2 (-(Δ f))) := by
  unfold IsFourierMul
  rw [show (𝓕 (toL2 f) : L2Space E) = toL2 (𝓕 f) from SchwartzMap.toLp_fourier_eq f,
    show (𝓕 (toL2 (-(Δ f))) : L2Space E) = toL2 (𝓕 (-(Δ f))) from SchwartzMap.toLp_fourier_eq _]
  filter_upwards [SchwartzMap.coeFn_toLp (F := ℂ) (𝓕 f) 2 volume,
    SchwartzMap.coeFn_toLp (F := ℂ) (𝓕 (-(Δ f))) 2 volume] with ξ h1 h2
  rw [show ((toL2 (𝓕 f) : L2Space E) : E → ℂ) ξ = 𝓕 f ξ from h1,
    show ((toL2 (𝓕 (-(Δ f))) : L2Space E) : E → ℂ) ξ = 𝓕 (-(Δ f)) ξ from h2,
    fourier_neg_laplacian_apply]

theorem freeLaplacian_symmetric :
    (freeLaplacian (E := E)).IsFormalAdjoint (freeLaplacian (E := E)) := by
  rintro ⟨-, f, rfl⟩ ⟨-, g, rfl⟩
  rw [freeLaplacian_apply' f _ rfl, freeLaplacian_apply' g _ rfl]
  exact (pairing_iff_isFourierMul _ _).mpr (isFourierMul_toL2 f) g

theorem isFourierMul_adjoint (y : (freeLaplacian (E := E)).adjoint.domain) :
    IsFourierMul (y : L2Space E) ((freeLaplacian (E := E)).adjoint y) := by
  refine (pairing_iff_isFourierMul _ _).mp fun f => ?_
  have h := LinearPMap.adjoint_isFormalAdjoint (T := freeLaplacian (E := E))
    dense_freeLaplacian_domain y ⟨toL2 f, mem_freeLaplacian_domain f⟩
  rwa [freeLaplacian_apply f] at h

theorem mem_adjoint_domain_iff (y : L2Space E) :
    y ∈ (freeLaplacian (E := E)).adjoint.domain ↔ ∃ w, IsFourierMul y w := by
  constructor
  · intro hy
    exact ⟨_, isFourierMul_adjoint ⟨y, hy⟩⟩
  · rintro ⟨w, hw⟩
    refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨w, ?_⟩
    rintro ⟨-, f, rfl⟩
    rw [freeLaplacian_apply' f _ rfl]
    exact (pairing_iff_isFourierMul _ _).mpr hw f

/-- The inner product of two `L²` functions, computed on the Fourier side. -/
theorem inner_eq_integral_fourier (u v : L2Space E) :
    inner ℂ u v = ∫ ξ, (starRingEnd ℂ) ((𝓕 u : L2Space E) ξ) * ((𝓕 v : L2Space E) ξ) := by
  rw [← MeasureTheory.Lp.inner_fourier_eq u v, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp [RCLike.inner_apply]
  ring

theorem adjoint_symmetric :
    (freeLaplacian (E := E)).adjoint.IsFormalAdjoint (freeLaplacian (E := E)).adjoint := by
  intro x y
  rw [inner_eq_integral_fourier ((freeLaplacian (E := E)).adjoint x) (y : L2Space E),
    inner_eq_integral_fourier (x : L2Space E) ((freeLaplacian (E := E)).adjoint y)]
  refine integral_congr_ae ?_
  filter_upwards [isFourierMul_adjoint x, isFourierMul_adjoint y] with ξ h1 h2
  rw [← h1, ← h2, map_mul, Complex.conj_ofReal]
  ring

theorem dense_adjoint_domain :
    Dense (((freeLaplacian (E := E)).adjoint.domain : Submodule ℂ (L2Space E)) : Set (L2Space E)) := by
  have hle : (freeLaplacian (E := E)) ≤ (freeLaplacian (E := E)).adjoint :=
    LinearPMap.IsFormalAdjoint.le_adjoint dense_freeLaplacian_domain freeLaplacian_symmetric
  exact Dense.mono hle.1 dense_freeLaplacian_domain

/-! ## The adjoint is self-adjoint -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem multiplier_nonneg (ξ : E) : 0 ≤ multiplier ξ := by
  unfold multiplier; positivity

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem multiplier_le_of_mem_closedBall (n : ℕ) {ξ : E} (hξ : ξ ∈ Metric.closedBall (0 : E) n) :
    multiplier ξ ≤ 4 * π ^ 2 * (n : ℝ) ^ 2 := by
  rw [Metric.mem_closedBall, dist_zero_right] at hξ
  have h1 : ‖ξ‖ ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith [norm_nonneg ξ]
  have h2 : (0:ℝ) ≤ 4 * π ^ 2 := by positivity
  unfold multiplier
  nlinarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_multiplier : Continuous fun ξ : E => (multiplier ξ : ℂ) := by
  unfold multiplier
  fun_prop

theorem memLp_conj {f : E → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun ξ => (starRingEnd ℂ) (f ξ)) 2 volume := by
  refine MemLp.of_le hf ?_ (Filter.Eventually.of_forall fun ξ => by simp)
  exact Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable

/-- If `u ∈ L²` vanishes outside a ball, then `multiplier · u ∈ L²`. -/
theorem memLp_multiplier_mul_of_support (n : ℕ) {u : E → ℂ} (hu : MemLp u 2 volume)
    (hsupp : ∀ ξ ∉ Metric.closedBall (0 : E) n, u ξ = 0) :
    MemLp (fun ξ => (multiplier ξ : ℂ) * u ξ) 2 volume := by
  refine MemLp.of_le (hu.const_mul (((4 * π ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ)))
    (continuous_multiplier.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ξ => ?_)
  by_cases hξ : ξ ∈ Metric.closedBall (0 : E) n
  · have hb1 : ‖(multiplier ξ : ℂ) * u ξ‖ = multiplier ξ * ‖u ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (multiplier_nonneg ξ)]
    have hb2 : ‖((4 * π ^ 2 * (n : ℝ) ^ 2 : ℝ) : ℂ) * u ξ‖ = (4 * π ^ 2 * (n : ℝ) ^ 2) * ‖u ξ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 4 * π ^ 2 * (n:ℝ) ^ 2)]
    rw [hb1, hb2]
    exact mul_le_mul_of_nonneg_right (multiplier_le_of_mem_closedBall n hξ) (norm_nonneg _)
  · simp [hsupp ξ hξ]

/-- Every `L²` function `u` such that `multiplier · u` is again in `L²` gives, via the inverse
Fourier transform, an element of the domain of the adjoint. -/
theorem exists_mem_adjoint_domain {u : E → ℂ} (hu : MemLp u 2 volume)
    (hmu : MemLp (fun ξ => (multiplier ξ : ℂ) * u ξ) 2 volume) :
    ∃ Y : (freeLaplacian (E := E)).adjoint.domain,
      (fun ξ => ((𝓕 (Y : L2Space E) : L2Space E) ξ)) =ᵐ[volume] u ∧
      (fun ξ => ((𝓕 ((freeLaplacian (E := E)).adjoint Y) : L2Space E) ξ)) =ᵐ[volume]
        fun ξ => (multiplier ξ : ℂ) * u ξ := by
  set Y : L2Space E := 𝓕⁻ (hu.toLp u) with hYdef
  have hFY : (𝓕 Y : L2Space E) = hu.toLp u := FourierTransform.fourier_fourierInv_eq _
  have hY1 : (fun ξ => ((𝓕 Y : L2Space E) ξ)) =ᵐ[volume] u := by
    rw [hFY]; exact hu.coeFn_toLp
  have hmem : Y ∈ (freeLaplacian (E := E)).adjoint.domain := by
    refine (mem_adjoint_domain_iff Y).mpr ⟨𝓕⁻ (hmu.toLp _), ?_⟩
    have hFw : (𝓕 (𝓕⁻ (hmu.toLp (fun ξ => (multiplier ξ : ℂ) * u ξ)) : L2Space E) : L2Space E)
        = hmu.toLp _ := FourierTransform.fourier_fourierInv_eq _
    unfold IsFourierMul
    rw [hFw]
    filter_upwards [hY1, hmu.coeFn_toLp] with ξ h1 h2
    rw [h1, h2]
  refine ⟨⟨Y, hmem⟩, hY1, ?_⟩
  have h := isFourierMul_adjoint (E := E) ⟨Y, hmem⟩
  unfold IsFourierMul at h
  filter_upwards [h, hY1] with ξ h1 h2
  rw [← h1, h2]

/-- The crucial step: if `w` represents the pairing of `z` against the whole adjoint operator,
then `w` is the multiplier applied to `z` on the Fourier side. -/
theorem isFourierMul_of_pairing_adjoint (z w : L2Space E)
    (h : ∀ Y : (freeLaplacian (E := E)).adjoint.domain,
      inner ℂ w (Y : L2Space E) = inner ℂ z ((freeLaplacian (E := E)).adjoint Y)) :
    IsFourierMul z w := by
  have hZm : MemLp (fun ξ => ((𝓕 z : L2Space E) ξ)) 2 volume := Lp.memLp _
  have hWm : MemLp (fun ξ => ((𝓕 w : L2Space E) ξ)) 2 volume := Lp.memLp _
  have key : ∀ n : ℕ, ∀ᵐ ξ ∂volume, (Metric.closedBall (0 : E) n).indicator
      (fun ξ => ((𝓕 w : L2Space E) ξ) - (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) ξ = 0 := by
    intro n
    set A : Set E := Metric.closedBall (0 : E) n with hA
    have hAmeas : MeasurableSet A := measurableSet_closedBall
    set u : E → ℂ := A.indicator
      (fun ξ => ((𝓕 w : L2Space E) ξ) - (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) with hudef
    have husupp : ∀ ξ ∉ A, u ξ = 0 := fun ξ hξ => Set.indicator_of_notMem hξ _
    have hu : MemLp u 2 volume := by
      have h1 : MemLp (A.indicator fun ξ => ((𝓕 w : L2Space E) ξ)) 2 volume :=
        hWm.indicator hAmeas
      have h2 : MemLp (A.indicator fun ξ => (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) 2 volume := by
        have h3 : MemLp (A.indicator fun ξ => ((𝓕 z : L2Space E) ξ)) 2 volume :=
          hZm.indicator hAmeas
        have h4 := memLp_multiplier_mul_of_support n h3
          (fun ξ hξ => Set.indicator_of_notMem hξ _)
        refine MemLp.ae_eq ?_ h4
        filter_upwards with ξ
        by_cases hξ : ξ ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hξ]
      have h5 : u = (A.indicator fun ξ => ((𝓕 w : L2Space E) ξ))
          - A.indicator (fun ξ => (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) := by
        funext ξ
        by_cases hξ : ξ ∈ A <;>
          simp [hudef, Set.indicator_of_mem, Set.indicator_of_notMem, hξ]
      rw [h5]
      exact h1.sub h2
    have hmu : MemLp (fun ξ => (multiplier ξ : ℂ) * u ξ) 2 volume :=
      memLp_multiplier_mul_of_support n hu husupp
    obtain ⟨Y, hY1, hY2⟩ := exists_mem_adjoint_domain hu hmu
    have hpair := h Y
    have hLHS : inner ℂ w (Y : L2Space E)
        = ∫ ξ, (starRingEnd ℂ) ((𝓕 w : L2Space E) ξ) * u ξ := by
      rw [inner_eq_integral_fourier]
      refine integral_congr_ae ?_
      filter_upwards [hY1] with ξ hξ
      rw [hξ]
    have hRHS : inner ℂ z ((freeLaplacian (E := E)).adjoint Y)
        = ∫ ξ, (starRingEnd ℂ) ((multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) * u ξ := by
      rw [inner_eq_integral_fourier]
      refine integral_congr_ae ?_
      filter_upwards [hY2] with ξ hξ
      rw [hξ, map_mul, Complex.conj_ofReal]
      ring
    have hint1 : Integrable
        (fun ξ => (starRingEnd ℂ) ((𝓕 w : L2Space E) ξ) * u ξ) volume := by
      simpa [Pi.mul_def] using (memLp_conj hWm).integrable_mul hu
    have hint2 : Integrable
        (fun ξ => (starRingEnd ℂ) ((multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) * u ξ) volume := by
      have h0 : Integrable
          (fun ξ => (starRingEnd ℂ) ((𝓕 z : L2Space E) ξ) * ((multiplier ξ : ℂ) * u ξ)) volume := by
        simpa [Pi.mul_def] using (memLp_conj hZm).integrable_mul hmu
      refine h0.congr ?_
      filter_upwards with ξ
      rw [map_mul, Complex.conj_ofReal]
      ring
    have hzero : ∫ ξ, (starRingEnd ℂ) (u ξ) * u ξ = 0 := by
      have hsplit : ∫ ξ, (starRingEnd ℂ) (u ξ) * u ξ
          = (∫ ξ, (starRingEnd ℂ) ((𝓕 w : L2Space E) ξ) * u ξ)
            - ∫ ξ, (starRingEnd ℂ) ((multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) * u ξ := by
        rw [← integral_sub hint1 hint2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        dsimp only
        by_cases hξ : ξ ∈ A
        · have hval : u ξ = ((𝓕 w : L2Space E) ξ) - (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ) :=
            Set.indicator_of_mem hξ _
          rw [hval, map_sub]
          ring
        · rw [husupp ξ hξ]
          ring
      rw [hsplit, ← hLHS, ← hRHS, hpair, sub_self]
    have hUzero : hu.toLp u = 0 := by
      refine inner_self_eq_zero (𝕜 := ℂ).mp ?_
      rw [MeasureTheory.L2.inner_def]
      rw [← hzero]
      refine integral_congr_ae ?_
      filter_upwards [hu.coeFn_toLp] with ξ hξ
      rw [hξ, RCLike.inner_apply]
      ring
    have : u =ᵐ[volume] 0 := by
      have h1 := hu.coeFn_toLp
      rw [hUzero] at h1
      filter_upwards [h1, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure E))] with ξ h2 h3
      rw [← h2, h3]
    filter_upwards [this] with ξ hξ using hξ
  have hall : ∀ᵐ ξ ∂volume, ∀ n : ℕ, (Metric.closedBall (0 : E) n).indicator
      (fun ξ => ((𝓕 w : L2Space E) ξ) - (multiplier ξ : ℂ) * ((𝓕 z : L2Space E) ξ)) ξ = 0 :=
    ae_all_iff.2 key
  filter_upwards [hall] with ξ hξ
  obtain ⟨n, hn⟩ := exists_nat_ge ‖ξ‖
  have h1 := hξ n
  rw [Set.indicator_of_mem (by simpa [Metric.mem_closedBall, dist_zero_right] using hn)] at h1
  exact (sub_eq_zero.mp h1).symm

theorem isFourierMul_unique {y w₁ w₂ : L2Space E} (h₁ : IsFourierMul y w₁)
    (h₂ : IsFourierMul y w₂) : w₁ = w₂ := by
  have hae : (fun ξ => ((𝓕 w₁ : L2Space E) ξ)) =ᵐ[volume] fun ξ => ((𝓕 w₂ : L2Space E) ξ) := by
    filter_upwards [h₁, h₂] with ξ e₁ e₂
    rw [← e₁, ← e₂]
  have hFeq : (𝓕 w₁ : L2Space E) = (𝓕 w₂ : L2Space E) := by
    exact Lp.ext hae
  calc w₁ = 𝓕⁻ (𝓕 w₁ : L2Space E) := (FourierTransform.fourierInv_fourier_eq w₁).symm
    _ = 𝓕⁻ (𝓕 w₂ : L2Space E) := by rw [hFeq]
    _ = w₂ := FourierTransform.fourierInv_fourier_eq w₂

theorem adjoint_adjoint_le :
    (freeLaplacian (E := E)).adjoint.adjoint ≤ (freeLaplacian (E := E)).adjoint := by
  have key : ∀ x : (freeLaplacian (E := E)).adjoint.adjoint.domain,
      IsFourierMul (x : L2Space E) ((freeLaplacian (E := E)).adjoint.adjoint x) := by
    intro x
    refine isFourierMul_of_pairing_adjoint _ _ fun Y => ?_
    exact LinearPMap.adjoint_isFormalAdjoint (T := (freeLaplacian (E := E)).adjoint)
      dense_adjoint_domain x Y
  refine ⟨fun z hz => ?_, ?_⟩
  · exact (mem_adjoint_domain_iff z).mpr ⟨_, key ⟨z, hz⟩⟩
  · rintro x y hxy
    refine isFourierMul_unique (key x) ?_
    have := isFourierMul_adjoint y
    rwa [← hxy] at this

/-- **The free Laplacian is essentially self-adjoint on the Schwartz space**, proved by
diagonalising it with the Fourier transform. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier :
    IsEssentiallySelfAdjoint (freeLaplacian (E := E)) := by
  refine ⟨dense_freeLaplacian_domain, freeLaplacian_symmetric, ?_⟩
  exact le_antisymm adjoint_adjoint_le
    (LinearPMap.IsFormalAdjoint.le_adjoint dense_adjoint_domain adjoint_symmetric)

/-- Unfolding of `IsSelfAdjoint` for partially defined operators: the adjoint of the adjoint
equals the adjoint. -/
example : IsSelfAdjoint (freeLaplacian (E := E)).adjoint ↔
    (freeLaplacian (E := E)).adjoint.adjoint = (freeLaplacian (E := E)).adjoint := Iff.rfl

/-- The free Laplacian on `L²(ℝᵈ)` is essentially self-adjoint on the Schwartz space. -/
theorem freeLaplacian_euclidean_essentiallySelfAdjoint (d : ℕ) :
    IsEssentiallySelfAdjoint (freeLaplacian (E := EuclideanSpace ℝ (Fin d))) :=
  freeLaplacian_essentiallySelfAdjoint_of_fourier

end Brockian.Weyl.FreeLaplacian2

