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
# The basic criterion for essential self-adjointness

This file develops the abstract operator-theoretic input for `Brockian.Weyl.FreeLaplacian2`:
a densely defined symmetric operator on a complex Hilbert space whose two deficiency ranges
`Ran (T + i)` and `Ran (T - i)` are dense has self-adjoint closure, i.e. it is
*essentially self-adjoint*.
-/

namespace Brockian.Weyl

open LinearPMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `x ↦ T x + z • x` on the domain of `T`. -/
def defOp (T : H →ₗ.[ℂ] H) (z : ℂ) : T.domain →ₗ[ℂ] H := T.toFun + z • T.domain.subtype

omit [CompleteSpace H] in
@[simp]
theorem defOp_apply (T : H →ₗ.[ℂ] H) (z : ℂ) (x : T.domain) :
    defOp T z x = T x + z • (x : H) := rfl

/-- The deficiency range `Ran (T + z)` of a partially defined operator `T`. -/
def defRange (T : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H := LinearMap.range (defOp T z)

omit [CompleteSpace H] in
theorem mem_defRange {T : H →ₗ.[ℂ] H} {z : ℂ} {y : H} :
    y ∈ defRange T z ↔ ∃ x : T.domain, T x + z • (x : H) = y := Iff.rfl

/-- A densely defined symmetric operator is closable. -/
theorem isClosable_of_isFormalAdjoint_self {T : H →ₗ.[ℂ] H}
    (hdom : Dense (T.domain : Set H)) (hsymm : T.IsFormalAdjoint T) : T.IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.2
    ⟨T†, LinearPMap.adjoint_isClosed hdom, LinearPMap.IsFormalAdjoint.le_adjoint hdom hsymm⟩

/-- The closure of a densely defined symmetric operator is contained in the adjoint. -/
theorem closure_le_adjoint {T : H →ₗ.[ℂ] H}
    (hdom : Dense (T.domain : Set H)) (hsymm : T.IsFormalAdjoint T) : T.closure ≤ T† := by
  have hcl : T.IsClosable := isClosable_of_isFormalAdjoint_self hdom hsymm
  have hc : IsClosed ((T†).graph : Set (H × H)) := LinearPMap.adjoint_isClosed hdom
  apply LinearPMap.le_of_le_graph
  rw [← hcl.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _
    (LinearPMap.le_graph_of_le (LinearPMap.IsFormalAdjoint.le_adjoint hdom hsymm)) hc

omit [CompleteSpace H] in
/-- Taking the adjoint of a submodule of `H × H` is insensitive to topological closure. -/
theorem submodule_adjoint_topologicalClosure (g : Submodule ℂ (H × H)) :
    g.topologicalClosure.adjoint = g.adjoint := by
  ext x
  simp only [Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    exact h a b (Submodule.le_topologicalClosure g hab)
  · intro h a b hab
    have hcont : Continuous fun p : H × H => inner ℂ p.2 x.1 - inner ℂ p.1 x.2 := by fun_prop
    have hset : (g : Set (H × H)) ⊆ {p : H × H | inner ℂ p.2 x.1 - inner ℂ p.1 x.2 = 0} :=
      fun p hp => h p.1 p.2 hp
    simpa using closure_minimal hset (isClosed_eq hcont continuous_const) hab

omit [CompleteSpace H] in
/-- The domain of the closure of a densely defined operator is dense. -/
theorem dense_domain_closure {T : H →ₗ.[ℂ] H} (hdom : Dense (T.domain : Set H)) :
    Dense (T.closure.domain : Set H) :=
  hdom.mono fun _ hx => T.le_closure.1 hx

/-- The adjoint of the closure is the adjoint. -/
theorem adjoint_closure_eq {T : H →ₗ.[ℂ] H} (hdom : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : (T.closure)† = T† := by
  have hcl : T.IsClosable := isClosable_of_isFormalAdjoint_self hdom hsymm
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_domain_closure hdom),
    LinearPMap.adjoint_graph_eq_graph_adjoint hdom, ← hcl.graph_closure_eq_closure_graph,
    submodule_adjoint_topologicalClosure]

omit [CompleteSpace H] in
/-- For a symmetric operator and purely imaginary `z`,
`‖T x + z • x‖ ^ 2 = ‖T x‖ ^ 2 + ‖z‖ ^ 2 * ‖x‖ ^ 2`. -/
theorem norm_add_smul_sq {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T) (x : T.domain) (z : ℂ)
    (hz : z.re = 0) : ‖T x + z • (x : H)‖ ^ 2 = ‖T x‖ ^ 2 + ‖z‖ ^ 2 * ‖(x : H)‖ ^ 2 := by
  have hreal : (starRingEnd ℂ) (inner ℂ (T x) (x : H)) = inner ℂ (T x) (x : H) := by
    rw [inner_conj_symm]; exact (hsymm x x).symm
  have hre : ((inner ℂ (T x) (x : H)) : ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  have h0 : (z * inner ℂ (T x) (x : H)).re = 0 := by rw [Complex.mul_re, hz, hre]; ring
  simp only [RCLike.re_to_complex, h0]
  rw [mul_pow]; ring

/-- If `T` is closed and symmetric, then its deficiency ranges (for unimodular purely imaginary
`z`) are closed. -/
theorem isClosed_defRange {T : H →ₗ.[ℂ] H} (hclosed : T.IsClosed)
    (hsymm : T.IsFormalAdjoint T) {z : ℂ} (hz : z.re = 0) (hz1 : ‖z‖ = 1) :
    IsClosed (defRange T z : Set H) := by
  have hG : IsClosed (T.graph : Set (H × H)) := hclosed
  haveI : CompleteSpace (T.graph : Set (H × H)) := hG.completeSpace_coe
  set L : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) + z • (ContinuousLinearMap.fst ℂ H H) with hL
  set f : (T.graph : Submodule ℂ (H × H)) →L[ℂ] H := L.comp T.graph.subtypeL with hf
  have hrange : Set.range f = (defRange T z : Set H) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx1, hx2⟩ := LinearPMap.mem_graph_iff T |>.mp p.2
      exact ⟨x, by simp [hf, hL, ← hx1, ← hx2]⟩
    · rintro ⟨x, rfl⟩
      refine ⟨⟨((x : H), T x), T.mem_graph x⟩, ?_⟩
      simp [hf, hL]
  rw [← hrange]
  have hanti : AntilipschitzWith 1 f := by
    apply AddMonoidHomClass.antilipschitz_of_bound
    intro p
    obtain ⟨x, hx1, hx2⟩ := LinearPMap.mem_graph_iff T |>.mp p.2
    have hfp : f p = T x + z • (x : H) := by simp [hf, hL, ← hx1, ← hx2]
    have hkey : ‖f p‖ ^ 2 = ‖T x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
      rw [hfp, norm_add_smul_sq hsymm x z hz, hz1]; ring
    have hp : ‖(p : H × H)‖ = max ‖(x : H)‖ ‖T x‖ := by rw [Prod.norm_def, ← hx1, ← hx2]
    have h1 : ‖(x : H)‖ ≤ ‖f p‖ := by
      nlinarith [norm_nonneg (f p), norm_nonneg (x : H), norm_nonneg (T x)]
    have h2 : ‖T x‖ ≤ ‖f p‖ := by
      nlinarith [norm_nonneg (f p), norm_nonneg (x : H), norm_nonneg (T x)]
    have hpp : ‖p‖ = ‖(p : H × H)‖ := rfl
    simp only [NNReal.coe_one, one_mul, hpp, hp]
    exact max_le h1 h2
  exact hanti.isClosed_range (ContinuousLinearMap.uniformContinuous f)

/-- The closure of a symmetric densely defined operator is symmetric. -/
theorem isFormalAdjoint_closure {T : H →ₗ.[ℂ] H} (hdom : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : T.closure.IsFormalAdjoint T.closure := by
  intro x y
  have hle : T.closure ≤ (T.closure)† := by
    rw [adjoint_closure_eq hdom hsymm]; exact closure_le_adjoint hdom hsymm
  have hx : (x : H) ∈ (T.closure)†.domain := hle.1 x.2
  have hval : T.closure x = (T.closure)† ⟨(x : H), hx⟩ := hle.2 rfl
  rw [hval]
  exact LinearPMap.adjoint_isFormalAdjoint (dense_domain_closure hdom) ⟨(x : H), hx⟩ y

/-- If the deficiency range of `T` is dense, the corresponding deficiency range of the closure
is everything. -/
theorem defRange_closure_eq_top {T : H →ₗ.[ℂ] H} (hdom : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) {z : ℂ} (hz : z.re = 0) (hz1 : ‖z‖ = 1)
    (hdense : Dense (defRange T z : Set H)) : defRange T.closure z = ⊤ := by
  have hcl : T.IsClosable := isClosable_of_isFormalAdjoint_self hdom hsymm
  have hsub : (defRange T z : Set H) ⊆ (defRange T.closure z : Set H) := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨(x : H), T.le_closure.1 x.2⟩, by rw [defOp_apply, defOp_apply, ← T.le_closure.2 rfl]⟩
  have hdense' : Dense (defRange T.closure z : Set H) := hdense.mono hsub
  have hclosed : IsClosed (defRange T.closure z : Set H) :=
    isClosed_defRange hcl.closure_isClosed (isFormalAdjoint_closure hdom hsymm) hz hz1
  have : (defRange T.closure z : Set H) = Set.univ := by
    rw [← hclosed.closure_eq, hdense'.closure_eq]
  exact SetLike.coe_injective (by simpa using this)

/-- **The basic criterion for essential self-adjointness**: a densely defined symmetric
operator whose two deficiency ranges are dense has self-adjoint closure. -/
theorem isSelfAdjoint_closure_of_dense_defRange {T : H →ₗ.[ℂ] H}
    (hdom : Dense (T.domain : Set H)) (hsymm : T.IsFormalAdjoint T)
    (hplus : Dense (defRange T Complex.I : Set H))
    (hminus : Dense (defRange T (-Complex.I) : Set H)) :
    IsSelfAdjoint T.closure := by
  have hIre : (Complex.I).re = 0 := by simp
  have hInorm : ‖Complex.I‖ = 1 := by simp
  have htop : defRange T.closure Complex.I = ⊤ :=
    defRange_closure_eq_top hdom hsymm hIre hInorm hplus
  have hCle : T.closure ≤ T† := closure_le_adjoint hdom hsymm
  -- every element of the domain of the adjoint lies in the domain of the closure
  have key : ∀ (v : H) (hv : v ∈ (T†).domain),
      ∃ u : T.closure.domain, (u : H) = v ∧ T† ⟨v, hv⟩ = T.closure u := by
    intro v hv
    obtain ⟨u, hu⟩ : ∃ u : T.closure.domain,
        T.closure u + Complex.I • (u : H) = T† ⟨v, hv⟩ + Complex.I • v := by
      have hmem : (T† ⟨v, hv⟩ + Complex.I • v) ∈ defRange T.closure Complex.I := by
        rw [htop]; trivial
      exact hmem
    have hgmem : v - (u : H) ∈ (T†).domain := Submodule.sub_mem _ hv (hCle.1 u.2)
    have hval : T† ⟨v - (u : H), hgmem⟩ = -Complex.I • (v - (u : H)) := by
      have h1 : T† ⟨v - (u : H), hgmem⟩ = T† ⟨v, hv⟩ - T† ⟨(u : H), hCle.1 u.2⟩ := by
        rw [← LinearPMap.map_sub]; rfl
      have h2 : T† ⟨(u : H), hCle.1 u.2⟩ = T.closure u := (hCle.2 rfl).symm
      have h3 : T† ⟨v, hv⟩ - T.closure u = Complex.I • (u : H) - Complex.I • v := by
        linear_combination (norm := module) -hu
      rw [h1, h2, h3, smul_sub]
      module
    have horth : ∀ w : defRange T (-Complex.I), inner ℂ (w : H) (v - (u : H)) = 0 := by
      rintro ⟨w, x, rfl⟩
      have hIF := LinearPMap.adjoint_isFormalAdjoint hdom ⟨v - (u : H), hgmem⟩ x
      rw [hval] at hIF
      have hzero : inner ℂ (v - (u : H)) (T x + (-Complex.I) • (x : H)) = 0 := by
        rw [inner_add_right, inner_smul_right, ← hIF, inner_smul_left]
        simp [Complex.conj_I]
      rw [← inner_conj_symm]
      simp only [defOp_apply] at hzero ⊢
      rw [hzero]
      simp
    have hg : v - (u : H) = 0 := Dense.eq_zero_of_inner_right hminus horth
    have hvu : (u : H) = v := by
      have := sub_eq_zero.mp hg
      exact this.symm
    refine ⟨u, hvu, ?_⟩
    have : T† ⟨v, hv⟩ + Complex.I • v = T.closure u + Complex.I • v := by
      rw [← hu, hvu]
    exact add_right_cancel this
  have hadj_le : T† ≤ T.closure := by
    constructor
    · intro v hv
      obtain ⟨u, hu1, -⟩ := key v hv
      rw [← hu1]
      exact u.2
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨u, hu1, hu2⟩ := key x hx
      have : u = ⟨y, hy⟩ := Subtype.ext (by rw [hu1]; exact hxy)
      rw [hu2, this]
  have heq : T† = T.closure := le_antisymm hadj_le hCle
  rw [LinearPMap.isSelfAdjoint_def, adjoint_closure_eq hdom hsymm, heq]

end Brockian.Weyl

/-
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import Brockian.Weyl.EssentialSelfAdjoint

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Complex FourierTransform Laplacian LineDeriv
open scoped Real ContDiff

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The Fourier transform of the Laplacian -/

variable {V}

/-- The Fourier transform turns a directional derivative into multiplication. -/
theorem fourier_lineDeriv_apply (u : 𝓢(V, ℂ)) (m : V) (ξ : V) :
    𝓕 (∂_{m} u) ξ = (2 * π * Complex.I) * ((inner ℝ ξ m : ℝ) : ℂ) * 𝓕 u ξ := by
  have h : ((fun x => inner ℝ x m : V → ℝ)).HasTemperateGrowth := by fun_prop
  rw [SchwartzMap.fourier_lineDerivOp_eq, SchwartzMap.smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply h]
  simp [Complex.real_smul]
  ring

/-- The Fourier transform turns the Laplacian into multiplication by `-4π²‖ξ‖²`. -/
theorem fourier_laplacian_apply (u : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (Δ u) ξ = -(4 * π ^ 2 * ‖ξ‖ ^ 2) * 𝓕 u ξ := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  have hsum : 𝓕 (∑ i, ∂_{b i} (∂_{b i} u)) = ∑ i, 𝓕 (∂_{b i} (∂_{b i} u)) := by simp
  rw [SchwartzMap.laplacian_eq_sum b u, hsum, SchwartzMap.sum_apply]
  have hterm : ∀ i, 𝓕 (∂_{b i} (∂_{b i} u)) ξ
      = -(4 * π ^ 2) * ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2 * 𝓕 u ξ := by
    intro i
    rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply]
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h2 : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := by
    have hb2 := b.sum_inner_mul_inner ξ ξ
    rw [← real_inner_self_eq_norm_sq, ← hb2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (b i) ξ]
    ring
  have hcast : ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2 = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h2]; push_cast; ring
  rw [hcast]; push_cast; ring

/-- Solvability of `(-Δ + z) u = 𝓕⁻ ψ` inside the Schwartz space, for `ψ` a compactly supported
Schwartz function and `z` non-real: on the Fourier side one simply divides by the nowhere
vanishing symbol `4π²‖ξ‖² + z`. -/
theorem exists_schwartz_solution {z : ℂ} (hz : z.im ≠ 0) (ψ : 𝓢(V, ℂ))
    (hψ : HasCompactSupport ψ) : ∃ u : 𝓢(V, ℂ), -(Δ u) + z • u = 𝓕⁻ ψ := by
  classical
  set m : V → ℂ := fun ξ => ((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + z with hm
  have hm0 : ∀ ξ, m ξ ≠ 0 := by
    intro ξ h
    apply hz
    have h2 : (m ξ).im = z.im := by simp only [hm, Complex.add_im, Complex.ofReal_im, zero_add]
    rw [← h2, h, Complex.zero_im]
  have hmsmooth : ContDiff ℝ ∞ m := by
    have h1 : ContDiff ℝ ∞ (fun ξ : V => (4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) := by
      have := (contDiff_norm_sq (E := V) (n := ∞) ℝ)
      fun_prop
    have h2 : ContDiff ℝ ∞ (fun ξ : V => ((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h1
    simp only [hm]
    exact h2.add contDiff_const
  have hsmooth : ContDiff ℝ ∞ (fun ξ => ψ ξ * (m ξ)⁻¹) :=
    (ψ.smooth ⊤).mul (hmsmooth.inv hm0)
  have hcs : HasCompactSupport (fun ξ => ψ ξ * (m ξ)⁻¹) := hψ.mul_right
  set φ : 𝓢(V, ℂ) := hcs.toSchwartzMap hsmooth with hφ
  refine ⟨𝓕⁻ φ, ?_⟩
  have hFw : 𝓕 (𝓕⁻ φ) = φ := fourier_fourierInv_eq φ
  have hF : 𝓕 (-(Δ (𝓕⁻ φ)) + z • (𝓕⁻ φ)) = ψ := by
    ext ξ
    have h1 : 𝓕 (-(Δ (𝓕⁻ φ)) + z • (𝓕⁻ φ)) = -(𝓕 (Δ (𝓕⁻ φ))) + z • 𝓕 (𝓕⁻ φ) := by simp
    rw [h1, SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
      fourier_laplacian_apply, hFw]
    have hφξ : φ ξ = ψ ξ * (m ξ)⁻¹ := by simp [hφ]
    have hmξ : m ξ = 4 * (π : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 + z := by
      simp only [hm]; push_cast; ring
    have hne : 4 * (π : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 + z ≠ 0 := by rw [← hmξ]; exact hm0 ξ
    rw [hφξ, hmξ, smul_eq_mul]
    field_simp
  calc -(Δ (𝓕⁻ φ)) + z • 𝓕⁻ φ = 𝓕⁻ (𝓕 (-(Δ (𝓕⁻ φ)) + z • 𝓕⁻ φ)) :=
        (fourierInv_fourier_eq _).symm
    _ = 𝓕⁻ ψ := by rw [hF]

variable (V)

/-! ### The free Laplacian as an unbounded operator on `L²` -/

/-- The Hilbert space `L²(V, ℂ)`. -/
abbrev L2Space := MeasureTheory.Lp (α := V) ℂ 2 volume

/-- The inclusion of the Schwartz space into `L²`. -/
noncomputable def toL2 : 𝓢(V, ℂ) →ₗ[ℂ] L2Space V :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

@[simp]
theorem toL2_apply (f : 𝓢(V, ℂ)) : toL2 V f = f.toLp 2 volume := rfl

theorem toL2_injective : Function.Injective (toL2 V) := by
  intro f g h
  have h1 : (f : V → ℂ) =ᵐ[volume] (g : V → ℂ) := by
    filter_upwards [f.coeFn_toLp 2 (volume : Measure V), g.coeFn_toLp 2 (volume : Measure V)]
      with x hx hy
    rw [← hx, ← hy]
    exact congrFun (congrArg (fun u : L2Space V => (u : V → ℂ)) h) x
  exact SchwartzMap.ext
    (congrFun ((Continuous.ae_eq_iff_eq volume f.continuous g.continuous).mp h1))

theorem denseRange_toL2 : DenseRange (toL2 V) :=
  SchwartzMap.denseRange_toLpCLM (E := V) (F := ℂ) (p := 2) (μ := volume) ENNReal.ofNat_ne_top

/-- The free Laplacian `-Δ` acting on the Schwartz space. -/
noncomputable def freeLaplacianSchwartz : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) :=
  -(laplacianCLM ℂ V 𝓢(V, ℂ)).toLinearMap

omit [MeasurableSpace V] [BorelSpace V] in
@[simp]
theorem freeLaplacianSchwartz_apply (f : 𝓢(V, ℂ)) : freeLaplacianSchwartz V f = -(Δ f) := by
  simp [freeLaplacianSchwartz]

/-- The free Laplacian `-Δ` as an unbounded operator on `L²(V, ℂ)` with the Schwartz space as
its domain. -/
noncomputable def freeLaplacian : L2Space V →ₗ.[ℂ] L2Space V where
  domain := LinearMap.range (toL2 V)
  toFun := (toL2 V ∘ₗ freeLaplacianSchwartz V) ∘ₗ
    (LinearEquiv.ofInjective (toL2 V) (toL2_injective V)).symm.toLinearMap

theorem freeLaplacian_domain : (freeLaplacian V).domain = LinearMap.range (toL2 V) := rfl

theorem mem_freeLaplacian_domain (f : 𝓢(V, ℂ)) : toL2 V f ∈ (freeLaplacian V).domain :=
  ⟨f, rfl⟩

theorem freeLaplacian_apply (f : 𝓢(V, ℂ)) (h : toL2 V f ∈ (freeLaplacian V).domain) :
    freeLaplacian V ⟨toL2 V f, h⟩ = toL2 V (-(Δ f)) := by
  have h2 : (LinearEquiv.ofInjective (toL2 V) (toL2_injective V)).symm ⟨toL2 V f, h⟩ = f :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  show (toL2 V ∘ₗ freeLaplacianSchwartz V)
      ((LinearEquiv.ofInjective (toL2 V) (toL2_injective V)).symm ⟨toL2 V f, h⟩) = _
  rw [h2]
  simp

theorem dense_freeLaplacian_domain : Dense ((freeLaplacian V).domain : Set (L2Space V)) := by
  have := denseRange_toL2 V
  simpa [freeLaplacian_domain, DenseRange, Set.range] using this

/-! ### Symmetry -/

theorem inner_toL2 (f g : 𝓢(V, ℂ)) :
    inner ℂ (toL2 V f) (toL2 V g) = ∫ x, (starRingEnd ℂ) (f x) * g x := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 (volume : Measure V), g.coeFn_toLp 2 (volume : Measure V)]
    with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

/-- The sesquilinear pairing `(a, b) ↦ conj a * b` on `ℂ`, as a real-bilinear map. -/
noncomputable def sesqMul : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap

theorem freeLaplacian_isSymmetric : (freeLaplacian V).IsFormalAdjoint (freeLaplacian V) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨f, rfl⟩ := hx
  obtain ⟨g, rfl⟩ := hy
  rw [freeLaplacian_apply, freeLaplacian_apply, inner_toL2, inner_toL2]
  have hIBP : ∫ x, (starRingEnd ℂ) (f x) * (Δ g) x = ∫ x, (starRingEnd ℂ) ((Δ f) x) * g x :=
    SchwartzMap.integral_bilinear_laplacian_right_eq_left f g sesqMul
  have h1 : ∀ x : V, (starRingEnd ℂ) ((-(Δ f)) x) * g x
      = -((starRingEnd ℂ) ((Δ f) x) * g x) := by
    intro x; simp
  have h2 : ∀ x : V, (starRingEnd ℂ) (f x) * ((-(Δ g)) x)
      = -((starRingEnd ℂ) (f x) * (Δ g) x) := by
    intro x; simp
  simp only [h1, h2, integral_neg, hIBP]

/-! ### Density of the deficiency ranges -/

theorem dense_compactSupport_toL2 :
    Dense {x : L2Space V | ∃ ψ : 𝓢(V, ℂ), HasCompactSupport ψ ∧ toL2 V ψ = x} := by
  have hd := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (E := V) (F := ℂ) (μ := volume)
    (p := 2) ENNReal.ofNat_ne_top
  refine hd.mono ?_
  rintro x ⟨g, hxg, hcs, hcd⟩
  refine ⟨hcs.toSchwartzMap hcd, by simpa using hcs, ?_⟩
  refine Lp.ext_iff.mpr ?_
  filter_upwards [(hcs.toSchwartzMap hcd).coeFn_toLp 2 (volume : Measure V), hxg] with y hy hy2
  rw [toL2_apply, hy, hy2]
  simp

theorem dense_defRange (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Brockian.Weyl.defRange (freeLaplacian V) z : Set (L2Space V)) := by
  set S : Set (L2Space V) := {x | ∃ ψ : 𝓢(V, ℂ), HasCompactSupport ψ ∧ toL2 V ψ = x}
  set e : L2Space V ≃ₜ L2Space V := (MeasureTheory.Lp.fourierTransformₗᵢ V ℂ).symm.toHomeomorph
  have hSdense : Dense S := dense_compactSupport_toL2 V
  have himage : Dense (e '' S) := by
    intro y
    rw [(e.image_closure S).symm, hSdense.closure_eq, Set.image_univ, e.surjective.range_eq]
    trivial
  refine Dense.mono ?_ himage
  rintro y ⟨x, ⟨ψ, hψ, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := exists_schwartz_solution hz ψ hψ
  refine ⟨⟨toL2 V u, mem_freeLaplacian_domain V u⟩, ?_⟩
  have hfi : e (toL2 V ψ) = toL2 V (𝓕⁻ ψ) := by
    show 𝓕⁻ (ψ.toLp 2 volume) = _
    rw [SchwartzMap.toLp_fourierInv_eq]
    rfl
  rw [Brockian.Weyl.defOp_apply, freeLaplacian_apply, hfi, ← hu]
  simp [map_add, map_smul]

/-! ### The main theorem -/

/-- **The free Laplacian is essentially self-adjoint.**  The operator `-Δ` with domain the
Schwartz space, viewed as an unbounded operator on `L²(V, ℂ)`, is symmetric, densely defined,
and its closure is self-adjoint.  The proof goes through the Fourier transform: it turns `-Δ`
into multiplication by `4π²‖ξ‖²`, so that `(-Δ ± i)` can be inverted on a dense set of data. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier :
    IsSelfAdjoint (freeLaplacian V).closure :=
  Brockian.Weyl.isSelfAdjoint_closure_of_dense_defRange (dense_freeLaplacian_domain V)
    (freeLaplacian_isSymmetric V)
    (dense_defRange V Complex.I (by simp))
    (dense_defRange V (-Complex.I) (by simp))

/-- Equivalently: the adjoint of the free Laplacian (defined on the Schwartz space) is exactly
its closure, so that `-Δ` has a unique self-adjoint extension. -/
theorem freeLaplacian_adjoint_eq_closure :
    LinearPMap.adjoint (freeLaplacian V) = (freeLaplacian V).closure := by
  rw [← Brockian.Weyl.adjoint_closure_eq (dense_freeLaplacian_domain V)
    (freeLaplacian_isSymmetric V)]
  exact freeLaplacian_essentiallySelfAdjoint_of_fourier V

end Brockian.Weyl.FreeLaplacian2

