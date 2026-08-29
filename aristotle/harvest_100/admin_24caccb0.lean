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

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real LineDeriv
open scoped FourierTransform InnerProductSpace Laplacian

noncomputable section

/-- A densely defined operator `A` on a Hilbert space is *essentially self-adjoint* if its
adjoint is self-adjoint (equivalently, if the closure `A** = A*` of `A` is self-adjoint). -/
def IsEssentiallySelfAdjoint {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] (A : E →ₗ.[𝕜] E) : Prop :=
  Dense (A.domain : Set E) ∧ IsSelfAdjoint A.adjoint

/-- The Fourier multiplier of the free Laplacian `-Δ`. -/
def multiplier {W : Type*} [NormedAddCommGroup W] (ξ : W) : ℝ := (2 * π) ^ 2 * ‖ξ‖ ^ 2

lemma continuous_multiplier {W : Type*} [NormedAddCommGroup W] :
    Continuous fun ξ : W => ((multiplier ξ : ℝ) : ℂ) := by
  unfold multiplier
  fun_prop

/-- The adjoint operation on unbounded operators is order-reversing. -/
lemma adjoint_antitone {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] {T S : E →ₗ.[𝕜] E}
    (hT : Dense (T.domain : Set E)) (hS : Dense (S.domain : Set E)) (h : S ≤ T) :
    T.adjoint ≤ S.adjoint := by
  have hmem : ∀ y : T.adjoint.domain, (y : E) ∈ S.adjoint.domain := by
    intro y
    refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨T.adjoint y, fun x => ?_⟩
    have hx : (x : E) ∈ T.domain := h.1 x.2
    have hSx : S x = T ⟨(x : E), hx⟩ := h.2 rfl
    rw [hSx]
    exact LinearPMap.adjoint_isFormalAdjoint hT y ⟨(x : E), hx⟩
  refine ⟨fun x hx => hmem ⟨x, hx⟩, ?_⟩
  rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ hyy
  subst hyy
  refine (LinearPMap.adjoint_apply_eq hS ⟨y₁, hy₂⟩ (x₀ := T.adjoint ⟨y₁, hy₁⟩) ?_).symm
  intro x
  have hx : (x : E) ∈ T.domain := h.1 x.2
  have hSx : S x = T ⟨(x : E), hx⟩ := h.2 rfl
  rw [hSx]
  exact LinearPMap.adjoint_isFormalAdjoint hT ⟨y₁, hy₁⟩ ⟨(x : E), hx⟩

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Hilbert space `L²(V, ℂ)`. -/
abbrev L2Space := Lp (α := V) ℂ 2 volume

/-- The inclusion of Schwartz functions into `L²`. -/
def toL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2Space V := (toLpCLM ℂ ℂ 2 volume).toLinearMap

@[simp] lemma toL2_apply (f : 𝓢(V, ℂ)) : toL2 V f = f.toLp 2 volume := rfl

lemma toL2_injective : Function.Injective (toL2 V) := SchwartzMap.injective_toLp 2 volume

/-- The free Laplacian `-Δ` on `L²(V, ℂ)`, with the Schwartz space as its domain. -/
def freeLaplacian : L2Space V →ₗ.[ℂ] L2Space V where
  domain := LinearMap.range (toL2 V)
  toFun := (toL2 V ∘ₗ (-(laplacianCLM ℂ V 𝓢(V, ℂ)).toLinearMap)) ∘ₗ
    (LinearEquiv.ofInjective (toL2 V) (toL2_injective V)).symm.toLinearMap

lemma mem_domain_freeLaplacian (f : 𝓢(V, ℂ)) : toL2 V f ∈ (freeLaplacian V).domain :=
  ⟨f, rfl⟩

lemma freeLaplacian_apply (f : 𝓢(V, ℂ)) :
    (freeLaplacian V) ⟨toL2 V f, mem_domain_freeLaplacian V f⟩ = toL2 V (-(Δ f)) := by
  have h : (LinearEquiv.ofInjective (toL2 V) (toL2_injective V)).symm
      ⟨toL2 V f, mem_domain_freeLaplacian V f⟩ = f := by
    apply (LinearEquiv.symm_apply_eq _).2
    exact Subtype.ext rfl
  show (toL2 V ∘ₗ (-(laplacianCLM ℂ V 𝓢(V, ℂ)).toLinearMap))
      ((LinearEquiv.ofInjective (toL2 V) (toL2_injective V)).symm
        ⟨toL2 V f, mem_domain_freeLaplacian V f⟩) = _
  rw [h]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.neg_apply,
    ContinuousLinearMap.coe_coe, SchwartzMap.laplacianCLM_eq, toL2_apply, map_neg]

lemma dense_domain_freeLaplacian : Dense ((freeLaplacian V).domain : Set (L2Space V)) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top
    (μ := (volume : Measure V))
  have hset : ((freeLaplacian V).domain : Set (L2Space V))
      = Set.range (toLpCLM ℝ ℂ 2 volume) := rfl
  rw [hset]
  exact h

/-- Multiplication of a Schwartz function by the Fourier multiplier of `-Δ`, realized as a
Schwartz function via the Fourier transform. -/
def mulMultiplier (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) := 𝓕 (-(Δ (𝓕⁻ φ)) : 𝓢(V, ℂ))

lemma fourier_laplacian_apply (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (Δ f : 𝓢(V, ℂ)) ξ = (-(multiplier ξ) : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  have hstep : ∀ (g : 𝓢(V, ℂ)) (m : V) (x : V),
      𝓕 (∂_{m} g) x = (2 * π * Complex.I * (inner ℝ x m)) * 𝓕 g x := by
    intro g m x
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    have hm : (fun y : V => (inner ℝ y m : ℝ)).HasTemperateGrowth := by fun_prop
    simp [hm]
    ring
  rw [SchwartzMap.laplacian_eq_sum b]
  have hsum : 𝓕 (∑ i, ∂_{b i} (∂_{b i} f) : 𝓢(V, ℂ))
      = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f) : 𝓢(V, ℂ)) := by
    change (fourierTransformCLM ℂ) _ = _
    rw [map_sum]
    rfl
  rw [hsum, SchwartzMap.sum_apply]
  have key : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f) : 𝓢(V, ℂ)) ξ
      = (-((2 * π) ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2 : ℝ) : ℂ) * 𝓕 f ξ := by
    intro i
    rw [hstep, hstep]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hnorm : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := b.sum_sq_inner_left ξ
  simp_rw [key]
  rw [← Finset.sum_mul]
  congr 1
  simp only [multiplier]
  push_cast
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  norm_cast
  rw [hnorm]

/-- The Fourier transform diagonalizes the free Laplacian: the Fourier transform of `-Δ f`
is the pointwise product of the multiplier `(2π)²‖ξ‖²` with the Fourier transform of `f`. -/
lemma fourier_neg_laplacian_apply (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (-(Δ f) : 𝓢(V, ℂ)) ξ = (multiplier ξ : ℂ) * 𝓕 f ξ := by
  have h : 𝓕 (-(Δ f) : 𝓢(V, ℂ)) = -(𝓕 (Δ f : 𝓢(V, ℂ))) := by
    change (fourierTransformCLM ℂ) _ = _
    rw [map_neg]
    rfl
  rw [h]
  simp [fourier_laplacian_apply]

lemma mulMultiplier_apply (φ : 𝓢(V, ℂ)) (ξ : V) :
    mulMultiplier V φ ξ = (multiplier ξ : ℂ) * φ ξ := by
  rw [mulMultiplier, fourier_neg_laplacian_apply, FourierTransform.fourier_fourierInv_eq]

lemma mulMultiplier_fourier (f : 𝓢(V, ℂ)) :
    mulMultiplier V (𝓕 f) = 𝓕 (-(Δ f) : 𝓢(V, ℂ)) := by
  rw [mulMultiplier, FourierTransform.fourierInv_fourier_eq]

lemma fourier_toL2 (f : 𝓢(V, ℂ)) : 𝓕 (toL2 V f) = toL2 V (𝓕 f) :=
  SchwartzMap.toLp_fourier_eq f

lemma inner_toL2 (u : L2Space V) (φ : 𝓢(V, ℂ)) :
    inner ℂ u (toL2 V φ) = ∫ ξ, (starRingEnd ℂ) ((u : V → ℂ) ξ) * φ ξ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp φ 2 (volume : Measure V)] with x hx
  simp [RCLike.inner_apply, toL2, hx, mul_comm]

lemma locallyIntegrable_of_L2 (u : L2Space V) : LocallyIntegrable (u : V → ℂ) volume :=
  (Lp.memLp u).locallyIntegrable one_le_two

lemma locallyIntegrable_multiplier_mul (u : L2Space V) :
    LocallyIntegrable (fun ξ => (multiplier ξ : ℂ) * (u : V → ℂ) ξ) volume := by
  have h : LocallyIntegrableOn (fun ξ : V => (u : V → ℂ) ξ * (multiplier ξ : ℂ)) Set.univ
      volume := by
    refine LocallyIntegrableOn.mul_continuousOn ?_ ?_ ?_
    · exact (locallyIntegrable_of_L2 V u).locallyIntegrableOn _
    · exact continuous_multiplier.continuousOn
    · exact isClosed_univ.isLocallyClosed
  rw [locallyIntegrableOn_univ] at h
  simpa [mul_comm] using h

/-- Key duality step: if `W` pairs against Schwartz functions like the multiplier multiple of
`G` does, then `W = multiplier • G` almost everywhere. -/
lemma ae_eq_multiplier_mul (G W : L2Space V)
    (h : ∀ φ : 𝓢(V, ℂ), inner ℂ W (toL2 V φ) = inner ℂ G (toL2 V (mulMultiplier V φ))) :
    (W : V → ℂ) =ᵐ[volume] fun ξ => (multiplier ξ : ℂ) * (G : V → ℂ) ξ := by
  refine ae_eq_of_integral_contDiff_smul_eq (locallyIntegrable_of_L2 V W)
    (locallyIntegrable_multiplier_mul V G) ?_
  intro g hg hgs
  have hcs : HasCompactSupport fun x => ((g x : ℝ) : ℂ) :=
    hgs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hcd : ContDiff ℝ (⊤ : ℕ∞) fun x => ((g x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hg
  set φ : 𝓢(V, ℂ) := hcs.toSchwartzMap hcd with hφ
  have hφa : ∀ x, φ x = ((g x : ℝ) : ℂ) := fun x => rfl
  have h1 := h φ
  rw [inner_toL2, inner_toL2] at h1
  have h2 : ∫ ξ, (starRingEnd ℂ) ((W : V → ℂ) ξ) * ((g ξ : ℝ) : ℂ)
      = ∫ ξ, (starRingEnd ℂ) ((G : V → ℂ) ξ) * ((multiplier ξ : ℂ) * ((g ξ : ℝ) : ℂ)) := by
    simpa [hφa, mulMultiplier_apply] using h1
  have h3 := congrArg (starRingEnd ℂ) h2
  rw [← integral_conj, ← integral_conj] at h3
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
    Complex.conj_ofReal] at h3
  calc ∫ x, g x • (W : V → ℂ) x
      = ∫ x, (W : V → ℂ) x * ((g x : ℝ) : ℂ) := by
        simp [Complex.real_smul, mul_comm]
    _ = ∫ x, (G : V → ℂ) x * ((multiplier x : ℂ) * ((g x : ℝ) : ℂ)) := h3
    _ = ∫ x, g x • ((multiplier x : ℂ) * (G : V → ℂ) x) := by
        simp [Complex.real_smul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

/-- The adjoint of the free Laplacian acts as multiplication by `(2π)²‖ξ‖²` on the Fourier
side. -/
lemma fourier_adjoint_apply (g : (freeLaplacian V).adjoint.domain) :
    ((𝓕 ((freeLaplacian V).adjoint g) : L2Space V) : V → ℂ)
      =ᵐ[volume] fun ξ => (multiplier ξ : ℂ) * ((𝓕 (g : L2Space V) : L2Space V) : V → ℂ) ξ := by
  refine ae_eq_multiplier_mul V _ _ ?_
  intro φ
  set f : 𝓢(V, ℂ) := 𝓕⁻ φ with hf
  have hfφ : 𝓕 f = φ := FourierTransform.fourier_fourierInv_eq φ
  have hform := LinearPMap.adjoint_isFormalAdjoint (dense_domain_freeLaplacian V) g
    ⟨toL2 V f, mem_domain_freeLaplacian V f⟩
  rw [freeLaplacian_apply] at hform
  have hL : inner ℂ (𝓕 ((freeLaplacian V).adjoint g) : L2Space V) (toL2 V φ)
      = inner ℂ ((freeLaplacian V).adjoint g) (toL2 V f) := by
    rw [← hfφ, ← fourier_toL2, MeasureTheory.Lp.inner_fourier_eq]
  have hR : inner ℂ (𝓕 (g : L2Space V) : L2Space V) (toL2 V (mulMultiplier V φ))
      = inner ℂ (g : L2Space V) (toL2 V (-(Δ f))) := by
    rw [← hfφ, mulMultiplier_fourier, ← fourier_toL2, MeasureTheory.Lp.inner_fourier_eq]
  rw [hL, hR]
  exact hform

lemma freeLaplacian_isFormalAdjoint_self :
    (freeLaplacian V).IsFormalAdjoint (freeLaplacian V) := by
  rintro ⟨-, f, rfl⟩ ⟨-, f', rfl⟩
  rw [freeLaplacian_apply, freeLaplacian_apply]
  have e1 : inner ℂ (toL2 V (-(Δ f))) (toL2 V f')
      = inner ℂ (toL2 V (𝓕 (-(Δ f)))) (toL2 V (𝓕 f')) := by
    rw [← fourier_toL2, ← fourier_toL2, MeasureTheory.Lp.inner_fourier_eq]
  have e2 : inner ℂ (toL2 V f) (toL2 V (-(Δ f')))
      = inner ℂ (toL2 V (𝓕 f)) (toL2 V (𝓕 (-(Δ f')))) := by
    rw [← fourier_toL2, ← fourier_toL2, MeasureTheory.Lp.inner_fourier_eq]
  rw [e1, e2, inner_toL2, inner_toL2]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (-(Δ f)) : 𝓢(V, ℂ)) 2 (volume : Measure V),
    SchwartzMap.coeFn_toLp (𝓕 f : 𝓢(V, ℂ)) 2 (volume : Measure V)] with x hx1 hx2
  rw [show ((toL2 V (𝓕 (-(Δ f))) : L2Space V) : V → ℂ) x = 𝓕 (-(Δ f) : 𝓢(V, ℂ)) x from hx1,
    show ((toL2 V (𝓕 f) : L2Space V) : V → ℂ) x = 𝓕 f x from hx2,
    fourier_neg_laplacian_apply, fourier_neg_laplacian_apply]
  simp [Complex.conj_ofReal]
  ring

lemma adjoint_isFormalAdjoint_self :
    (freeLaplacian V).adjoint.IsFormalAdjoint (freeLaplacian V).adjoint := by
  intro g₁ g₂
  have h1 : inner ℂ ((freeLaplacian V).adjoint g₁) (g₂ : L2Space V)
      = inner ℂ (𝓕 ((freeLaplacian V).adjoint g₁) : L2Space V)
        (𝓕 (g₂ : L2Space V) : L2Space V) := (MeasureTheory.Lp.inner_fourier_eq _ _).symm
  have h2 : inner ℂ (g₁ : L2Space V) ((freeLaplacian V).adjoint g₂)
      = inner ℂ (𝓕 (g₁ : L2Space V) : L2Space V)
        (𝓕 ((freeLaplacian V).adjoint g₂) : L2Space V) := (MeasureTheory.Lp.inner_fourier_eq _ _).symm
  rw [h1, h2, MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fourier_adjoint_apply V g₁, fourier_adjoint_apply V g₂] with x hx1 hx2
  rw [RCLike.inner_apply, RCLike.inner_apply, hx1, hx2]
  simp [Complex.conj_ofReal]
  ring

/-- **The free Laplacian is essentially self-adjoint on the Schwartz space**, proved by
Fourier diagonalization: on the Fourier side `-Δ` becomes multiplication by `(2π)²‖ξ‖²`. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier :
    IsEssentiallySelfAdjoint (freeLaplacian V) := by
  refine ⟨dense_domain_freeLaplacian V, ?_⟩
  have hdense := dense_domain_freeLaplacian V
  have hle : freeLaplacian V ≤ (freeLaplacian V).adjoint :=
    (freeLaplacian_isFormalAdjoint_self V).le_adjoint hdense
  have hdense' : Dense (((freeLaplacian V).adjoint.domain : Submodule ℂ (L2Space V)) :
      Set (L2Space V)) :=
    hdense.mono (fun _ hx => hle.1 hx)
  have h1 : (freeLaplacian V).adjoint ≤ (freeLaplacian V).adjoint.adjoint :=
    (adjoint_isFormalAdjoint_self V).le_adjoint hdense'
  have h2 : (freeLaplacian V).adjoint.adjoint ≤ (freeLaplacian V).adjoint :=
    adjoint_antitone hdense' hdense hle
  exact LinearPMap.isSelfAdjoint_def.2 (le_antisymm h2 h1)

/-- The free Laplacian on `L²(ℝ^d, ℂ)` is essentially self-adjoint on the Schwartz space. -/
theorem freeLaplacian_essentiallySelfAdjoint_euclidean (d : ℕ) :
    IsEssentiallySelfAdjoint (freeLaplacian (EuclideanSpace ℝ (Fin d))) :=
  freeLaplacian_essentiallySelfAdjoint_of_fourier _

end

end Brockian.Weyl.FreeLaplacian2

