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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap ComplexInnerProductSpace FourierTransform Laplacian Real

namespace Brockian.FreeLaplacianPlancherel

noncomputable section

/-! ## An abstract criterion for essential self-adjointness

We work with a symmetric, densely defined operator `T` with domain a submodule `D` of a complex
Hilbert space `H`.  Mathlib does not (yet) have a theory of unbounded operators, so we spell out
the relevant notions.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `IsAdjointPair D T y z` says that `y` belongs to the domain of the adjoint of the operator
`T` (with domain `D`) and that `z` is a corresponding adjoint value, i.e.
`⟪T x, y⟫ = ⟪x, z⟫` for all `x` in the domain.  If `D` is dense then `z` is uniquely determined
by `y`, and `z = T* y`. -/
def IsAdjointPair (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) (y z : H) : Prop :=
  ∀ x : D, ⟪T x, y⟫ = ⟪(x : H), z⟫

/-- A densely defined operator `T` with domain `D` in a complex Hilbert space is *essentially
self-adjoint* if it is symmetric and its adjoint `T*` is symmetric as well.

(Since `D` is dense, the adjoint is a well-defined operator; `adjoint_symmetric` states exactly
that `⟪T* y₁, y₂⟫ = ⟪y₁, T* y₂⟫` for all `y₁, y₂` in the domain of `T*`.  For a densely defined
symmetric operator this is the standard characterisation of essential self-adjointness: it is
equivalent to the closure of `T` being self-adjoint, because `T*** = T*` and `T** = closure T`.) -/
structure IsEssentiallySelfAdjoint (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Prop where
  dense_domain : Dense (D : Set H)
  symmetric : ∀ x y : D, ⟪T x, (y : H)⟫ = ⟪(x : H), T y⟫
  adjoint_symmetric : ∀ y₁ z₁ y₂ z₂ : H, IsAdjointPair D T y₁ z₁ → IsAdjointPair D T y₂ z₂ →
      ⟪z₁, y₂⟫ = ⟪y₁, z₂⟫

variable {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}

omit [CompleteSpace H] in
/-- For a symmetric operator, `‖(T + i)x‖² = ‖T x‖² + ‖x‖²`. -/
theorem norm_add_I_sq (hsym : ∀ x y : D, ⟪T x, (y : H)⟫ = ⟪(x : H), T y⟫) (x : D) :
    ‖T x + Complex.I • (x : H)‖ ^ 2 = ‖T x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  have h2 : (starRingEnd ℂ) ⟪T x, (x : H)⟫ = ⟪T x, (x : H)⟫ := by
    rw [inner_conj_symm]; exact (hsym x x).symm
  rw [norm_add_pow_two (𝕜 := ℂ), inner_smul_right]
  have hre : RCLike.re (Complex.I * ⟪T x, (x : H)⟫) = 0 := by
    have him : (⟪T x, (x : H)⟫).im = 0 := Complex.conj_eq_iff_im.mp h2
    simp [him]
  rw [hre]
  simp [norm_smul]

/-- **Basic criterion for essential self-adjointness**: a densely defined symmetric operator
whose ranges `Ran(T + i)` and `Ran(T - i)` are both dense is essentially self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_dense_range
    (hdense : Dense (D : Set H))
    (hsym : ∀ x y : D, ⟪T x, (y : H)⟫ = ⟪(x : H), T y⟫)
    (hplus : Dense (Set.range fun x : D => T x + Complex.I • (x : H)))
    (hminus : Dense (Set.range fun x : D => T x - Complex.I • (x : H))) :
    IsEssentiallySelfAdjoint D T := by
  refine ⟨hdense, hsym, ?_⟩
  have hplus' : DenseRange (fun x : D => T x + Complex.I • (x : H)) := hplus
  have hminus' : DenseRange (fun x : D => T x - Complex.I • (x : H)) := hminus
  intro y₁ z₁ y₂ z₂ h1 h2
  have hsq : ∀ x : D, ‖T x + Complex.I • (x : H)‖ ^ 2 = ‖T x‖ ^ 2 + ‖(x : H)‖ ^ 2 :=
    norm_add_I_sq hsym
  set Sp : D →ₗ[ℂ] H := T + Complex.I • D.subtype with hSp
  have hSpapp : ∀ x : D, Sp x = T x + Complex.I • (x : H) := by intro x; simp [hSp]
  have hb1 : ∀ x : D, ‖(D.subtype) x‖ ≤ 1 * ‖Sp x‖ := by
    intro x
    have h := hsq x
    rw [hSpapp]
    show ‖(x : H)‖ ≤ 1 * ‖T x + Complex.I • (x : H)‖
    nlinarith [norm_nonneg (T x + Complex.I • (x : H)), norm_nonneg (T x), norm_nonneg ((x : H))]
  have hb2 : ∀ x : D, ‖T x‖ ≤ 1 * ‖Sp x‖ := by
    intro x
    have h := hsq x
    rw [hSpapp]
    nlinarith [norm_nonneg (T x + Complex.I • (x : H)), norm_nonneg (T x), norm_nonneg ((x : H))]
  have hdr : DenseRange (Sp : D → H) := by
    have : (Sp : D → H) = fun x : D => T x + Complex.I • (x : H) := by funext x; exact hSpapp x
    rw [this]; exact hplus'
  set A : H →L[ℂ] H := (D.subtype).extendOfNorm Sp with hA
  set B : H →L[ℂ] H := T.extendOfNorm Sp with hB
  have hAeq : ∀ x : D, A (Sp x) = (x : H) := fun x => LinearMap.extendOfNorm_eq hdr ⟨1, hb1⟩ x
  have hBeq : ∀ x : D, B (Sp x) = T x := fun x => LinearMap.extendOfNorm_eq hdr ⟨1, hb2⟩ x
  have key1 : ∀ v : H, B v + Complex.I • A v = v := by
    have : (fun v => B v + Complex.I • A v) = (id : H → H) := by
      refine hdr.equalizer (by fun_prop) continuous_id ?_
      funext x
      show B (Sp x) + Complex.I • A (Sp x) = id (Sp x)
      rw [hAeq, hBeq, hSpapp]
      rfl
    exact fun v => congrFun this v
  have key2 : ∀ y z : H, (∀ x : D, ⟪T x, y⟫ = ⟪(x : H), z⟫) → ∀ v : H, ⟪B v, y⟫ = ⟪A v, z⟫ := by
    intro y z hyz
    have : (fun v => ⟪B v, y⟫) = (fun v => ⟪A v, z⟫) := by
      refine hdr.equalizer (by fun_prop) (by fun_prop) ?_
      funext x
      show ⟪B (Sp x), y⟫ = ⟪A (Sp x), z⟫
      rw [hAeq, hBeq]
      exact hyz x
    exact fun v => congrFun this v
  have key3 : ∀ (x : D) (v : H), ⟪T x, A v⟫ = ⟪(x : H), B v⟫ := by
    intro x
    have : (fun v => ⟪T x, A v⟫) = (fun v => ⟪(x : H), B v⟫) := by
      refine hdr.equalizer (by fun_prop) (by fun_prop) ?_
      funext y
      show ⟪T x, A (Sp y)⟫ = ⟪(x : H), B (Sp y)⟫
      rw [hAeq, hBeq]
      exact hsym x y
    exact fun v => congrFun this v
  set v : H := z₁ + Complex.I • y₁ with hv
  set g : H := A v with hg
  set w : H := B v with hw
  have hvg : w + Complex.I • g = z₁ + Complex.I • y₁ := key1 v
  have hu : y₁ - g = 0 := by
    have horth : ∀ x : D, ⟪T x - Complex.I • (x : H), y₁ - g⟫ = 0 := by
      intro x
      have e1 : ⟪T x, y₁ - g⟫ = ⟪(x : H), z₁ - w⟫ := by
        rw [inner_sub_right, inner_sub_right, h1 x, key3 x v]
      have e2 : z₁ - w = -(Complex.I • (y₁ - g)) := by
        rw [smul_sub]
        linear_combination (norm := module) -hvg
      rw [inner_sub_left, e1, e2, inner_neg_right, inner_smul_right, inner_smul_left]
      simp
    have hzero : (fun x : H => ⟪x, y₁ - g⟫) = (fun _ : H => (0 : ℂ)) := by
      refine hminus'.equalizer (by fun_prop) (by fun_prop) ?_
      funext x
      exact horth x
    exact inner_self_eq_zero.mp (congrFun hzero (y₁ - g))
  have hy1 : y₁ = g := by linear_combination (norm := module) hu
  have hz1 : z₁ = w := by
    rw [← hy1] at hvg
    linear_combination (norm := module) -hvg
  rw [hz1, hy1, hw, hg]
  exact key2 y₂ z₂ h2 v

end Abstract

/-! ## The free Laplacian on `L²(V)`

`V` is a finite-dimensional real inner product space (e.g. `EuclideanSpace ℝ (Fin d)`), equipped
with its Haar measure `volume`, and `H = L²(V, ℂ)`.
-/

section Concrete

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The multiplier `4π²‖ξ‖²` of the free Laplacian on the Fourier side. -/
def symb (ξ : V) : ℝ := 4 * π ^ 2 * ‖ξ‖ ^ 2

/-! ### Fourier transform of derivatives -/

/-- The Fourier transform turns a directional derivative into multiplication by `2πi⟪ξ, v⟫`. -/
theorem fourier_lineDeriv_apply (f : 𝓢(V, ℂ)) (v : V) (ξ : V) :
    (𝓕 (LineDeriv.lineDerivOp v f)) ξ = 2 * π * Complex.I * ((inner ℝ ξ v : ℝ) : ℂ) * (𝓕 f) ξ := by
  have e2 := SchwartzMap.fourier_lineDerivOp_eq (E := ℂ) f v
  have ht : (inner ℝ · v : V → ℝ).HasTemperateGrowth := by fun_prop
  rw [e2]
  simp [SchwartzMap.smulLeftCLM_apply_apply ht]
  ring

/-- The Fourier transform turns the Laplacian into multiplication by `-4π²‖ξ‖²`. -/
theorem fourier_laplacian_apply (f : 𝓢(V, ℂ)) (ξ : V) :
    (𝓕 (Δ f)) ξ = -((symb ξ : ℝ) : ℂ) * (𝓕 f) ξ := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  have h1 : (Δ f : 𝓢(V, ℂ)) = ∑ i, LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) f) :=
    SchwartzMap.laplacian_eq_sum b f
  have h2 : (𝓕 (Δ f) : 𝓢(V, ℂ))
      = ∑ i, 𝓕 (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) f)) := by
    rw [← SchwartzMap.fourierTransformCLM_apply ℂ, h1, map_sum]
    simp
  rw [h2, SchwartzMap.sum_apply]
  have h3 : ∀ i, (𝓕 (LineDeriv.lineDerivOp (b i) (LineDeriv.lineDerivOp (b i) f))) ξ
      = -((4 * π ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2 : ℝ) : ℂ) * (𝓕 f) ξ := by
    intro i
    rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  simp_rw [h3]
  rw [← Finset.sum_mul]
  congr 1
  have hsum : ∑ i, -((4 * π ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2 : ℝ) : ℂ)
      = -((4 * π ^ 2 * ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [hsum, OrthonormalBasis.sum_sq_inner_left]
  rfl

/-- The Fourier transform of `-Δ f + c f` is multiplication by `4π²‖ξ‖² + c`. -/
theorem fourier_shift_apply (c : ℂ) (f : 𝓢(V, ℂ)) (ξ : V) :
    (𝓕 ((-Δ f) + c • f)) ξ = (((symb ξ : ℝ) : ℂ) + c) * (𝓕 f) ξ := by
  have h : (𝓕 ((-Δ f) + c • f) : 𝓢(V, ℂ)) = -(𝓕 (Δ f)) + c • (𝓕 f) := by
    rw [← SchwartzMap.fourierTransformCLM_apply ℂ, map_add, map_neg, map_smul]
    simp
  rw [h]
  simp only [SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
    fourier_laplacian_apply, smul_eq_mul]
  ring

/-! ### Inner products of Schwartz functions in `L²` -/

theorem inner_toLp (f : 𝓢(V, ℂ)) (w : Lp (α := V) ℂ 2 volume) :
    ⟪f.toLp 2 volume, w⟫ = ∫ x, (starRingEnd ℂ) (f x) * (w x) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp f 2 volume] with x hx
  rw [hx, RCLike.inner_apply']

theorem inner_toLp_toLp (f g : 𝓢(V, ℂ)) :
    ⟪f.toLp 2 volume, g.toLp 2 volume⟫ = ∫ x, (starRingEnd ℂ) (f x) * g x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp f 2 volume, SchwartzMap.coeFn_toLp g 2 volume]
    with x hx hy
  rw [hx, hy, RCLike.inner_apply']

/-- Symmetry of the Laplacian on Schwartz functions, by integration by parts. -/
theorem inner_toLp_laplacian (f g : 𝓢(V, ℂ)) :
    ⟪(Δ f).toLp 2 volume, g.toLp 2 volume⟫ = ⟪f.toLp 2 volume, (Δ g).toLp 2 volume⟫ := by
  rw [inner_toLp_toLp, inner_toLp_toLp]
  have := SchwartzMap.integral_bilinear_laplacian_right_eq_left (μ := (volume : Measure V)) f g
    ((ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ))
  simpa using this.symm

/-! ### Density of the ranges, via Plancherel -/

/-- If `w ∈ L²` is such that `∫ conj((4π²‖ξ‖² + c) φ(ξ)) w(ξ) dξ = 0` for every Schwartz function
`φ`, and `4π²‖ξ‖² + c` never vanishes, then `w = 0`. -/
theorem eq_zero_of_integral_eq_zero (c : ℂ) (hc : ∀ ξ : V, ((symb ξ : ℝ) : ℂ) + c ≠ 0)
    (w : Lp (α := V) ℂ 2 volume)
    (hw : ∀ φ : 𝓢(V, ℂ), ∫ ξ, (starRingEnd ℂ) ((((symb ξ : ℝ) : ℂ) + c) * φ ξ) * (w ξ) = 0) :
    w = 0 := by
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hli : LocallyIntegrable (fun ξ => (w ξ : ℂ)) volume :=
    (Lp.memLp w).locallyIntegrable one_le_two
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hli ?_
  intro g hg_smooth hg_supp
  set ψ : V → ℂ := fun ξ => (g ξ : ℂ) * ((((symb ξ : ℝ) : ℂ) + c))⁻¹ with hψ
  have hden : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : V => (((symb ξ : ℝ) : ℂ) + c)) := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : V => (symb ξ : ℝ)) :=
      contDiff_const.mul (contDiff_norm_sq ℝ)
    exact (Complex.ofRealCLM.contDiff.comp this).add contDiff_const
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    ContDiff.mul (Complex.ofRealCLM.contDiff.comp hg_smooth) (hden.inv hc)
  have hsupp : HasCompactSupport ψ :=
    HasCompactSupport.mul_right (hg_supp.comp_left (g := fun r : ℝ => (r : ℂ)) rfl)
  set φ : 𝓢(V, ℂ) := hsupp.toSchwartzMap hsmooth with hφ
  have hφapp : ∀ ξ, φ ξ = ψ ξ := fun ξ => HasCompactSupport.toSchwartzMap_toFun hsupp hsmooth ξ
  rw [← hw φ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show g ξ • (w ξ : ℂ) = (starRingEnd ℂ) ((((symb ξ : ℝ) : ℂ) + c) * φ ξ) * (w ξ)
  rw [hφapp ξ, hψ]
  simp only
  rw [← mul_assoc, mul_comm ((((symb ξ : ℝ) : ℂ) + c)) ((g ξ : ℂ)), mul_assoc,
    mul_inv_cancel₀ (hc ξ), mul_one]
  simp [Complex.real_smul]

/-- If `u ∈ L²` is orthogonal to `(-Δ + c)𝓢(V)`, then `u = 0`.  This is the Plancherel step: on
the Fourier side the operator becomes multiplication by the nowhere vanishing function
`4π²‖ξ‖² + c`. -/
theorem eq_zero_of_orthogonal (c : ℂ) (hc : ∀ ξ : V, ((symb ξ : ℝ) : ℂ) + c ≠ 0)
    (u : Lp (α := V) ℂ 2 volume)
    (h0 : ∀ f : 𝓢(V, ℂ), ⟪((-Δ f) + c • f).toLp 2 volume, u⟫ = 0) : u = 0 := by
  have hw : ∀ φ : 𝓢(V, ℂ),
      ∫ ξ, (starRingEnd ℂ) ((((symb ξ : ℝ) : ℂ) + c) * φ ξ) *
        ((𝓕 u : Lp (α := V) ℂ 2 volume) ξ) = 0 := by
    intro φ
    obtain ⟨f, hf⟩ : ∃ f : 𝓢(V, ℂ), 𝓕 f = φ := ⟨𝓕⁻ φ, FourierTransform.fourier_fourierInv_eq φ⟩
    have h1 : ⟪𝓕 (((-Δ f) + c • f).toLp 2 volume), 𝓕 u⟫ = 0 := by
      rw [Lp.inner_fourier_eq]; exact h0 f
    rw [SchwartzMap.toLp_fourier_eq, inner_toLp] at h1
    rw [← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [fourier_shift_apply c f ξ, hf]
  have hfu : (𝓕 u : Lp (α := V) ℂ 2 volume) = 0 := eq_zero_of_integral_eq_zero c hc _ hw
  have : ‖u‖ = 0 := by
    rw [← Lp.norm_fourier_eq u, hfu, norm_zero]
  exact norm_eq_zero.mp this

/-- Density of the range of `-Δ + c` on Schwartz functions, for `c` with `4π²‖ξ‖² + c ≠ 0`. -/
theorem dense_range_shift (c : ℂ) (hc : ∀ ξ : V, ((symb ξ : ℝ) : ℂ) + c ≠ 0) :
    Dense (Set.range fun f : 𝓢(V, ℂ) => ((-Δ f) + c • f).toLp 2 volume) := by
  set Ψ : 𝓢(V, ℂ) →L[ℂ] Lp (α := V) ℂ 2 volume :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp
      (-(LineDeriv.laplacianCLM ℂ V 𝓢(V, ℂ)) + c • ContinuousLinearMap.id ℂ 𝓢(V, ℂ)) with hΨ
  have hΨapp : ∀ f, Ψ f = ((-Δ f) + c • f).toLp 2 volume := by
    intro f
    simp only [hΨ, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.id_apply,
      SchwartzMap.laplacianCLM_eq, SchwartzMap.toLpCLM_apply]
  set K : Submodule ℂ (Lp (α := V) ℂ 2 volume) := LinearMap.range (Ψ : 𝓢(V, ℂ) →ₗ[ℂ] _) with hK
  have hrange : (Set.range fun f : 𝓢(V, ℂ) => ((-Δ f) + c • f).toLp 2 volume) = (K : Set _) := by
    ext v
    simp only [hK, SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    constructor
    · rintro ⟨f, rfl⟩; exact ⟨f, hΨapp f⟩
    · rintro ⟨f, rfl⟩; exact ⟨f, (hΨapp f).symm⟩
  rw [hrange, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  refine eq_zero_of_orthogonal c hc u fun f => ?_
  have hmem : Ψ f ∈ K := LinearMap.mem_range_self _ f
  have := (Submodule.mem_orthogonal K u).mp hu (Ψ f) hmem
  rwa [hΨapp f] at this

/-! ### The free Laplacian as an operator with Schwartz domain -/

theorem toLp_neg (f : 𝓢(V, ℂ)) :
    ((-f : 𝓢(V, ℂ))).toLp 2 volume = -(f.toLp 2 volume) := by
  simp only [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_neg]

theorem toLp_add (f g : 𝓢(V, ℂ)) :
    ((f + g : 𝓢(V, ℂ))).toLp 2 volume = f.toLp 2 volume + g.toLp 2 volume := by
  simp only [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_add]

theorem toLp_smul (c : ℂ) (f : 𝓢(V, ℂ)) :
    ((c • f : 𝓢(V, ℂ))).toLp 2 volume = c • f.toLp 2 volume := by
  simp only [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_smul]

/-- The Schwartz space, viewed as a (dense) subspace of `L²(V, ℂ)`: the domain of the free
Laplacian. -/
def schwartzDomain : Submodule ℂ (Lp (α := V) ℂ 2 volume) :=
  LinearMap.range ((SchwartzMap.toLpCLM ℂ ℂ 2 volume : 𝓢(V, ℂ) →L[ℂ] _) : 𝓢(V, ℂ) →ₗ[ℂ] _)

theorem injective_toLp_lm :
    Function.Injective ((SchwartzMap.toLpCLM ℂ ℂ 2 volume : 𝓢(V, ℂ) →L[ℂ] _) :
      𝓢(V, ℂ) →ₗ[ℂ] Lp (α := V) ℂ 2 volume) := by
  intro f g hfg
  exact SchwartzMap.injective_toLp (E := V) (F := ℂ) 2 volume (by simpa using hfg)

/-- The Schwartz space is linearly isomorphic to the domain of the free Laplacian, via `toLp`. -/
def schwartzEquiv : 𝓢(V, ℂ) ≃ₗ[ℂ] schwartzDomain (V := V) :=
  LinearEquiv.ofInjective _ (injective_toLp_lm (V := V))

theorem schwartzEquiv_apply (f : 𝓢(V, ℂ)) :
    ((schwartzEquiv f : schwartzDomain (V := V)) : Lp (α := V) ℂ 2 volume) = f.toLp 2 volume := rfl

theorem schwartzEquiv_symm_apply (f : 𝓢(V, ℂ)) (hx : f.toLp 2 volume ∈ schwartzDomain (V := V)) :
    schwartzEquiv.symm (⟨f.toLp 2 volume, hx⟩ : schwartzDomain (V := V)) = f := by
  apply schwartzEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext (schwartzEquiv_apply f)

theorem mem_schwartzDomain (f : 𝓢(V, ℂ)) : f.toLp 2 volume ∈ schwartzDomain (V := V) :=
  ⟨f, rfl⟩

/-- The free Laplacian `-Δ`, as a linear operator from the Schwartz domain to `L²(V, ℂ)`. -/
def freeLaplacian : schwartzDomain (V := V) →ₗ[ℂ] Lp (α := V) ℂ 2 volume :=
  (((SchwartzMap.toLpCLM ℂ ℂ 2 volume).comp
      (-(LineDeriv.laplacianCLM ℂ V 𝓢(V, ℂ)))) : 𝓢(V, ℂ) →ₗ[ℂ] _).comp
    (schwartzEquiv (V := V)).symm.toLinearMap

@[simp]
theorem freeLaplacian_apply (f : 𝓢(V, ℂ)) (hx : f.toLp 2 volume ∈ schwartzDomain (V := V)) :
    freeLaplacian (⟨f.toLp 2 volume, hx⟩ : schwartzDomain (V := V)) = (-Δ f).toLp 2 volume := by
  simp only [freeLaplacian, LinearMap.comp_apply, LinearEquiv.coe_coe, schwartzEquiv_symm_apply]
  rw [toLp_neg]
  simp

/-- Every element of the domain is of the form `f.toLp` for a Schwartz function `f`. -/
theorem exists_schwartz (x : schwartzDomain (V := V)) :
    ∃ f : 𝓢(V, ℂ), (x : Lp (α := V) ℂ 2 volume) = f.toLp 2 volume := by
  obtain ⟨f, hf⟩ := x.2
  exact ⟨f, hf.symm⟩

theorem dense_schwartzDomain : Dense (schwartzDomain (V := V) : Set (Lp (α := V) ℂ 2 volume)) := by
  have h := SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ) (p := 2) (μ := (volume : Measure V))
    (by simp)
  have hset : Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure V))
      = (schwartzDomain (V := V) : Set (Lp (α := V) ℂ 2 volume)) := by
    ext v
    simp only [Set.mem_range, SetLike.mem_coe, schwartzDomain, LinearMap.mem_range]
    constructor
    · rintro ⟨f, rfl⟩; exact ⟨f, rfl⟩
    · rintro ⟨f, rfl⟩; exact ⟨f, rfl⟩
  rw [← hset]
  exact h

/-- The free Laplacian is symmetric on its Schwartz domain. -/
theorem freeLaplacian_symmetric (x y : schwartzDomain (V := V)) :
    ⟪freeLaplacian x, (y : Lp (α := V) ℂ 2 volume)⟫
      = ⟪(x : Lp (α := V) ℂ 2 volume), freeLaplacian y⟫ := by
  obtain ⟨f, hf⟩ := exists_schwartz x
  obtain ⟨g, hg⟩ := exists_schwartz y
  have hx : x = ⟨f.toLp 2 volume, hf ▸ x.2⟩ := Subtype.ext hf
  have hy : y = ⟨g.toLp 2 volume, hg ▸ y.2⟩ := Subtype.ext hg
  rw [hx, hy, freeLaplacian_apply, freeLaplacian_apply, toLp_neg, toLp_neg,
    inner_neg_left, inner_neg_right, inner_toLp_laplacian]

/-- The range of `-Δ + c` on the Schwartz domain, described via Schwartz functions. -/
theorem range_eq (c : ℂ) :
    (Set.range fun x : schwartzDomain (V := V) =>
        freeLaplacian x + c • (x : Lp (α := V) ℂ 2 volume))
      = Set.range fun f : 𝓢(V, ℂ) => ((-Δ f) + c • f).toLp 2 volume := by
  ext v
  simp only [Set.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨f, hf⟩ := exists_schwartz x
    have hx : x = ⟨f.toLp 2 volume, hf ▸ x.2⟩ := Subtype.ext hf
    refine ⟨f, ?_⟩
    rw [hx, freeLaplacian_apply, toLp_add, toLp_smul]
  · rintro ⟨f, rfl⟩
    refine ⟨⟨f.toLp 2 volume, mem_schwartzDomain f⟩, ?_⟩
    rw [freeLaplacian_apply, toLp_add, toLp_smul]

/-- **The free Laplacian `-Δ` on `L²(V, ℂ)`, with the Schwartz functions as its domain, is
essentially self-adjoint.**  The proof is via Plancherel's theorem: the Fourier transform turns
`-Δ + c` into multiplication by the nowhere-vanishing function `4π²‖ξ‖² + c` for `c = ±i`, which
gives the density of the deficiency ranges. -/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel :
    IsEssentiallySelfAdjoint (schwartzDomain (V := V)) freeLaplacian := by
  refine isEssentiallySelfAdjoint_of_dense_range dense_schwartzDomain freeLaplacian_symmetric
    ?_ ?_
  · have hc : ∀ ξ : V, ((symb ξ : ℝ) : ℂ) + Complex.I ≠ 0 := by
      intro ξ h
      have := congrArg Complex.im h
      simp at this
    rw [range_eq Complex.I]
    exact dense_range_shift Complex.I hc
  · have hc : ∀ ξ : V, ((symb ξ : ℝ) : ℂ) + (-Complex.I) ≠ 0 := by
      intro ξ h
      have := congrArg Complex.im h
      simp at this
    have hd := dense_range_shift (V := V) (-Complex.I) hc
    have hrw : (Set.range fun x : schwartzDomain (V := V) =>
        freeLaplacian x - Complex.I • (x : Lp (α := V) ℂ 2 volume))
        = Set.range fun f : 𝓢(V, ℂ) => ((-Δ f) + (-Complex.I) • f).toLp 2 volume := by
      rw [← range_eq (-Complex.I)]
      congr 1
      funext x
      rw [neg_smul, ← sub_eq_add_neg]
    rw [hrw]
    exact hd

/-- The free Laplacian on `L²(ℝ^d, ℂ)` with Schwartz domain is essentially self-adjoint. -/
theorem freeLaplacian_euclidean_essentiallySelfAdjoint (d : ℕ) :
    IsEssentiallySelfAdjoint (schwartzDomain (V := EuclideanSpace ℝ (Fin d))) freeLaplacian :=
  freeLaplacian_essentiallySelfAdjoint_via_plancherel

end Concrete

end

end Brockian.FreeLaplacianPlancherel

