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
/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open MeasureTheory SchwartzMap FourierTransform Complex
open scoped ComplexInnerProductSpace

namespace Brockian.FreeLaplacianPlancherel

/-! ## Abstract theory of graphs of unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The graph of the adjoint of the (not necessarily bounded) operator whose graph is `G`:
the set of pairs `(g, h)` with `⟪T f, g⟫ = ⟪f, h⟫` for all `(f, T f) ∈ G`. -/
def adjointGraph (G : Submodule ℂ (H × H)) : Submodule ℂ (H × H) where
  carrier := {q | ∀ p ∈ G, ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫}
  add_mem' := by
    intro a b ha hb p hp
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, ha p hp, hb p hp]
  zero_mem' := by intro p hp; simp
  smul_mem' := by
    intro c a ha p hp
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, ha p hp]

omit [CompleteSpace H] in
@[simp] lemma mem_adjointGraph {G : Submodule ℂ (H × H)} {q : H × H} :
    q ∈ adjointGraph G ↔ ∀ p ∈ G, ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫ := Iff.rfl

/-- A graph is symmetric if it is contained in the graph of its adjoint. -/
def IsSymmetricGraph (G : Submodule ℂ (H × H)) : Prop := G ≤ adjointGraph G

/-- An operator is essentially self-adjoint when the graph of its adjoint coincides with the
closure of its graph (equivalently, the closure of the operator is self-adjoint). -/
def IsEssentiallySelfAdjointGraph (G : Submodule ℂ (H × H)) : Prop :=
  adjointGraph G = G.topologicalClosure

omit [CompleteSpace H] in
lemma isClosed_adjointGraph (G : Submodule ℂ (H × H)) :
    IsClosed ((adjointGraph G : Submodule ℂ (H × H)) : Set (H × H)) := by
  have h : ((adjointGraph G : Submodule ℂ (H × H)) : Set (H × H))
      = ⋂ p ∈ (G : Set (H × H)), {q : H × H | ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫} := by
    ext q
    simp [adjointGraph]
  rw [h]
  refine isClosed_biInter fun p _ => ?_
  exact isClosed_eq (by fun_prop) (by fun_prop)

omit [CompleteSpace H] in
lemma adjointGraph_topologicalClosure (G : Submodule ℂ (H × H)) :
    adjointGraph G.topologicalClosure = adjointGraph G := by
  apply le_antisymm
  · intro q hq p hp
    exact hq p (G.le_topologicalClosure hp)
  · intro q hq p hp
    have hsub : (G : Set (H × H)) ⊆ {p : H × H | ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫} := fun r hr => hq r hr
    have hclosed : IsClosed {p : H × H | ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have := closure_minimal hsub hclosed
    exact this (by rwa [← Submodule.topologicalClosure_coe])

omit [CompleteSpace H] in
/-- Symmetry extends from a graph to its closure. -/
lemma inner_symm_of_mem_closure {G : Submodule ℂ (H × H)} (hsym : IsSymmetricGraph G)
    {p q : H × H} (hp : p ∈ G.topologicalClosure) (hq : q ∈ G.topologicalClosure) :
    ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫ := by
  have hcl : G.topologicalClosure ≤ adjointGraph G :=
    Submodule.topologicalClosure_minimal _ hsym (isClosed_adjointGraph G)
  have hq' : q ∈ adjointGraph G.topologicalClosure := by
    rw [adjointGraph_topologicalClosure]; exact hcl hq
  exact hq' p hp

/-- The "basic criterion": a symmetric operator whose ranges under `T ± i` are dense
(here phrased as: nothing nonzero is orthogonal to them) is essentially self-adjoint. -/
theorem isEssentiallySelfAdjointGraph_of_range_dense (G : Submodule ℂ (H × H))
    (hsym : IsSymmetricGraph G)
    (hplus : ∀ w : H, (∀ p ∈ G, ⟪p.2 + Complex.I • p.1, w⟫ = 0) → w = 0)
    (hminus : ∀ w : H, (∀ p ∈ G, ⟪p.2 - Complex.I • p.1, w⟫ = 0) → w = 0) :
    IsEssentiallySelfAdjointGraph G := by
  classical
  set S : Submodule ℂ (H × H) := G.topologicalClosure with hS
  have hcl : S ≤ adjointGraph G :=
    Submodule.topologicalClosure_minimal _ hsym (isClosed_adjointGraph G)
  -- the continuous linear map `p ↦ p.2 - I • p.1`
  set Φ : (H × H) →L[ℂ] H :=
    ContinuousLinearMap.snd ℂ H H - Complex.I • ContinuousLinearMap.fst ℂ H H with hΦ
  have hΦapply : ∀ p : H × H, Φ p = p.2 - Complex.I • p.1 := by
    intro p; simp [hΦ]
  -- the key norm identity on the closure of the graph
  have hnorm : ∀ p ∈ S, ‖p‖ ≤ ‖Φ p‖ := by
    intro p hp
    have hsymp : ⟪p.2, p.1⟫ = ⟪p.1, p.2⟫ := inner_symm_of_mem_closure hsym hp hp
    have him : (⟪p.1, p.2⟫ : ℂ).im = 0 := by
      have hconj : (starRingEnd ℂ) ⟪p.1, p.2⟫ = ⟪p.1, p.2⟫ := by
        rw [inner_conj_symm, hsymp]
      have := congrArg Complex.im hconj
      simp only [Complex.conj_im] at this
      linarith
    have hre : (RCLike.re (⟪p.2, Complex.I • p.1⟫ : ℂ)) = 0 := by
      rw [inner_smul_right, hsymp]
      simp [him]
    have hsq : ‖Φ p‖ ^ 2 = ‖p.2‖ ^ 2 + ‖p.1‖ ^ 2 := by
      rw [hΦapply p, @norm_sub_sq ℂ, hre]
      simp [norm_smul]
    have h1 : ‖p‖ = max ‖p.1‖ ‖p.2‖ := rfl
    have hle : ‖p‖ ^ 2 ≤ ‖Φ p‖ ^ 2 := by
      rw [hsq, h1]
      rcases max_cases ‖p.1‖ ‖p.2‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith [norm_nonneg p.1,
        norm_nonneg p.2]
    nlinarith [norm_nonneg (Φ p), norm_nonneg p, hle]
  -- `Φ` restricted to the closure of the graph has closed range
  have hSclosed : IsClosed (S : Set (H × H)) := Submodule.isClosed_topologicalClosure G
  haveI : CompleteSpace S := hSclosed.completeSpace_coe
  set f : S → H := fun x => Φ (x : H × H) with hf
  have hanti : AntilipschitzWith 1 f := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hxy : ((x : H × H) - (y : H × H)) ∈ S := S.sub_mem x.2 y.2
    have h := hnorm _ hxy
    rw [map_sub] at h
    simpa [Subtype.dist_eq, dist_eq_norm, hf] using h
  have hcont : UniformContinuous f :=
    Φ.uniformContinuous.comp uniformContinuous_subtype_val
  have hclosedrange : IsClosed (Set.range f) := hanti.isClosed_range hcont
  have hrangeeq : Set.range f = ((Submodule.map (Φ : (H × H) →ₗ[ℂ] H) S : Submodule ℂ H) : Set H) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : H × H), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  -- density of the range of `Φ` on the graph itself
  have hWtop : (Submodule.map (Φ : (H × H) →ₗ[ℂ] H) G).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro w hw
    refine hminus w fun p hp => ?_
    have hmem : Φ p ∈ Submodule.map (Φ : (H × H) →ₗ[ℂ] H) G := ⟨p, hp, rfl⟩
    have := (Submodule.mem_orthogonal _ _).1 hw (Φ p) hmem
    rwa [hΦapply] at this
  have hmapS : Submodule.map (Φ : (H × H) →ₗ[ℂ] H) S = ⊤ := by
    have h1 : Submodule.map (Φ : (H × H) →ₗ[ℂ] H) G ≤ Submodule.map (Φ : (H × H) →ₗ[ℂ] H) S :=
      Submodule.map_mono G.le_topologicalClosure
    have h2 : IsClosed ((Submodule.map (Φ : (H × H) →ₗ[ℂ] H) S : Submodule ℂ H) : Set H) := hrangeeq ▸ hclosedrange
    have h3 := Submodule.topologicalClosure_minimal _ h1 h2
    rw [hWtop] at h3
    exact top_unique h3
  refine le_antisymm ?_ hcl
  intro q hq
  obtain ⟨p, hpS, hpq⟩ : ∃ p ∈ S, Φ p = q.2 - Complex.I • q.1 := by
    have hmem : (q.2 - Complex.I • q.1) ∈ Submodule.map (Φ : (H × H) →ₗ[ℂ] H) S := by rw [hmapS]; trivial
    obtain ⟨p, hp, h⟩ := hmem
    exact ⟨p, hp, h⟩
  have hqp : q - p ∈ adjointGraph G := (adjointGraph G).sub_mem hq (hcl hpS)
  have hzero : (q - p).2 = Complex.I • (q - p).1 := by
    have h := hΦapply p
    rw [hpq] at h
    simp only [Prod.fst_sub, Prod.snd_sub, smul_sub]
    rw [sub_eq_sub_iff_sub_eq_sub] at h
    exact h.symm ▸ (by rw [← h])
  have hw : (q - p).1 = 0 := by
    refine hplus _ fun r hr => ?_
    have h1 : ⟪r.2, (q - p).1⟫ = ⟪r.1, (q - p).2⟫ := hqp r hr
    rw [inner_add_left, h1, hzero, inner_smul_right, inner_smul_left]
    simp [Complex.conj_I]
  have hq2 : (q - p).2 = 0 := by rw [hzero, hw, smul_zero]
  have hqeq : q = p := by
    have h1 : q.1 = p.1 := sub_eq_zero.1 (by simpa using hw)
    have h2 : q.2 = p.2 := sub_eq_zero.1 (by simpa using hq2)
    exact Prod.ext_iff.mpr ⟨h1, h2⟩
  rw [hqeq]
  exact hpS

end Abstract

/-! ## The free Laplacian on the line -/

section Concrete

open Real

/-- The Hilbert space `L²(ℝ, ℂ)` for Lebesgue measure. -/
abbrev L2R : Type := Lp (α := ℝ) ℂ 2

/-- The free Laplacian `-d²/dx²`, acting on Schwartz functions. -/
noncomputable def freeLaplacian : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  -(SchwartzMap.derivCLM ℂ ℂ ∘L SchwartzMap.derivCLM ℂ ℂ)

/-- The inclusion of the Schwartz space into `L²(ℝ, ℂ)`. -/
noncomputable def toL2 : 𝓢(ℝ, ℂ) →L[ℂ] L2R := SchwartzMap.toLpCLM ℂ ℂ 2 volume

/-- The multiplier `4π²ξ²` which the free Laplacian becomes on the Fourier side. -/
noncomputable def laplacianSymbol (x : ℝ) : ℝ := 4 * Real.pi ^ 2 * x ^ 2

/-- The graph of the free Laplacian with domain the Schwartz space, as a subspace of
`L²(ℝ, ℂ) × L²(ℝ, ℂ)`. -/
noncomputable def freeLaplacianGraph : Submodule ℂ (L2R × L2R) :=
  LinearMap.range ((toL2.prod (toL2 ∘L freeLaplacian) : 𝓢(ℝ, ℂ) →L[ℂ] (L2R × L2R)) :
    𝓢(ℝ, ℂ) →ₗ[ℂ] (L2R × L2R))

lemma mem_freeLaplacianGraph (f : 𝓢(ℝ, ℂ)) :
    ((toL2 f, toL2 (freeLaplacian f)) : L2R × L2R) ∈ freeLaplacianGraph :=
  ⟨f, rfl⟩

/-! ### The Fourier transform turns the Laplacian into multiplication by `4π²ξ²` -/

lemma fourier_derivCLM (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 g : 𝓢(ℝ, ℂ)) x * (2 * Real.pi * Complex.I * x)
      = (𝓕 (SchwartzMap.derivCLM ℂ ℂ g) : 𝓢(ℝ, ℂ)) x := by
  have hcoe : (⇑(SchwartzMap.derivCLM ℂ ℂ g)) = deriv (⇑g) := by
    ext y; simp [SchwartzMap.derivCLM_apply]
  have h1 : ((𝓕 (SchwartzMap.derivCLM ℂ ℂ g) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = 𝓕 (⇑(SchwartzMap.derivCLM ℂ ℂ g)) := SchwartzMap.fourier_coe _
  have h2 : ((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = 𝓕 (⇑g) := SchwartzMap.fourier_coe _
  rw [congrFun h1 x, congrFun h2 x, hcoe,
    Real.fourier_deriv g.integrable g.differentiable
      (by rw [← hcoe]; exact (SchwartzMap.derivCLM ℂ ℂ g).integrable)]
  simp [smul_eq_mul]
  ring

lemma fourier_freeLaplacian (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 (freeLaplacian g) : 𝓢(ℝ, ℂ)) x = ((laplacianSymbol x : ℝ) : ℂ) * (𝓕 g : 𝓢(ℝ, ℂ)) x := by
  have hneg : (𝓕 (freeLaplacian g) : 𝓢(ℝ, ℂ))
      = -(𝓕 (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ g)) : 𝓢(ℝ, ℂ)) := by
    have hg : freeLaplacian g = -(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ g)) := rfl
    rw [hg, ← SchwartzMap.fourierTransformCLM_apply ℂ, map_neg,
      SchwartzMap.fourierTransformCLM_apply]
  rw [hneg]
  have e1 := fourier_derivCLM (SchwartzMap.derivCLM ℂ ℂ g) x
  have e2 := fourier_derivCLM g x
  simp only [SchwartzMap.neg_apply, laplacianSymbol]
  rw [← e1, ← e2]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ### `L²` bookkeeping -/

lemma fourier_toL2 (f : 𝓢(ℝ, ℂ)) : 𝓕 (toL2 f) = toL2 (𝓕 f) := by
  simp [toL2, SchwartzMap.toLpCLM_apply, SchwartzMap.toLp_fourier_eq]

lemma coeFn_toL2 (u : 𝓢(ℝ, ℂ)) : ((toL2 u : L2R) : ℝ → ℂ) =ᶠ[ae volume] ⇑u := by
  have : (toL2 u : L2R) = u.toLp 2 volume := by simp [toL2, SchwartzMap.toLpCLM_apply]
  rw [this]
  exact SchwartzMap.coeFn_toLp (μ := volume) u 2

lemma inner_toL2 (u : 𝓢(ℝ, ℂ)) (v : L2R) :
    ⟪toL2 u, v⟫ = ∫ x : ℝ, (starRingEnd ℂ) (u x) * (v x) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 u] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

lemma inner_toL2_toL2 (u v : 𝓢(ℝ, ℂ)) :
    ⟪toL2 u, toL2 v⟫ = ∫ x : ℝ, (starRingEnd ℂ) (u x) * v x := by
  rw [inner_toL2]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 v] with x hx
  rw [hx]

/-! ### Symmetry -/

lemma isSymmetricGraph_freeLaplacianGraph : IsSymmetricGraph freeLaplacianGraph := by
  rintro p ⟨f, rfl⟩ q ⟨g, rfl⟩
  show ⟪toL2 (freeLaplacian g), toL2 f⟫ = ⟪toL2 g, toL2 (freeLaplacian f)⟫
  rw [← MeasureTheory.Lp.inner_fourier_eq (toL2 (freeLaplacian g)) (toL2 f),
    ← MeasureTheory.Lp.inner_fourier_eq (toL2 g) (toL2 (freeLaplacian f)),
    fourier_toL2, fourier_toL2, fourier_toL2, fourier_toL2,
    inner_toL2_toL2, inner_toL2_toL2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [fourier_freeLaplacian, fourier_freeLaplacian]
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-! ### Density of the ranges of `T ± i` -/

lemma locallyIntegrable_mul_of_continuous {g : ℝ → ℂ} (hg : Continuous g) {f : ℝ → ℂ}
    (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun x => g x * f x) volume := by
  intro x
  obtain ⟨u, hu, hfu⟩ := hf x
  obtain ⟨V, hVu, hVopen, hxV⟩ := mem_nhds_iff.1 hu
  have hWopen : IsOpen (V ∩ Metric.ball x 1) := hVopen.inter Metric.isOpen_ball
  refine ⟨V ∩ Metric.ball x 1, hWopen.mem_nhds ⟨hxV, Metric.mem_ball_self one_pos⟩, ?_⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hg.continuousOn
  refine (hfu.mono_set (fun y hy => hVu hy.1)).bdd_mul (c := C)
    hg.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
  exact hC y (Metric.ball_subset_closedBall hy.2)

lemma orthogonal_shift_eq_zero (z : ℂ) (hz : z.im ≠ 0) (w : L2R)
    (h : ∀ p ∈ freeLaplacianGraph, ⟪p.2 + z • p.1, w⟫ = 0) : w = 0 := by
  set u : L2R := 𝓕 w with hu
  -- Step 1: on the Fourier side the hypothesis says that `(m + conj z) * u` kills every
  -- Schwartz test function.
  have key : ∀ φ : 𝓢(ℝ, ℂ), ∫ x : ℝ, (starRingEnd ℂ) (φ x) *
      ((((laplacianSymbol x : ℝ) : ℂ) + (starRingEnd ℂ) z) * (u x)) = 0 := by
    intro φ
    obtain ⟨f, hf⟩ : ∃ f : 𝓢(ℝ, ℂ), (𝓕 f : 𝓢(ℝ, ℂ)) = φ :=
      ⟨𝓕⁻ φ, fourier_fourierInv_eq φ⟩
    have h0 := h _ (mem_freeLaplacianGraph f)
    simp only at h0
    rw [← MeasureTheory.Lp.inner_fourier_eq (toL2 (freeLaplacian f) + z • toL2 f) w,
      FourierAdd.fourier_add, fourier_smul, fourier_toL2, fourier_toL2, ← map_smul toL2 z,
      ← map_add, inner_toL2] at h0
    rw [← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, fourier_freeLaplacian, hf, smul_eq_mul]
    simp only [map_add, map_mul, Complex.conj_ofReal]
    ring
  -- Step 2: hence `(m + conj z) * u = 0` almost everywhere.
  have hcont : Continuous fun x : ℝ => (((laplacianSymbol x : ℝ) : ℂ) + (starRingEnd ℂ) z) := by
    unfold laplacianSymbol
    fun_prop
  have hloc : LocallyIntegrable
      (fun x : ℝ => (((laplacianSymbol x : ℝ) : ℂ) + (starRingEnd ℂ) z) * (u x)) volume :=
    locallyIntegrable_mul_of_continuous hcont
      ((MeasureTheory.Lp.memLp u).locallyIntegrable one_le_two)
  have hae : ∀ᵐ x : ℝ ∂volume,
      (((laplacianSymbol x : ℝ) : ℂ) + (starRingEnd ℂ) z) * (u x) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun χ hχ hχc => ?_
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ χ) := Complex.ofRealCLM.contDiff.comp hχ
    have hcs : HasCompactSupport (Complex.ofRealCLM ∘ χ) := hχc.comp_left rfl
    rw [← key (hcs.toSchwartzMap hsm)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  -- Step 3: `m x + conj z` never vanishes, so `u = 0` and therefore `w = 0`.
  have hu0 : u = 0 := by
    rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hae] with x hx
    rcases mul_eq_zero.1 hx with h1 | h2
    · exfalso
      apply hz
      have := congrArg Complex.im h1
      simpa using this
    · exact h2
  have hnorm : ‖w‖ = 0 := by
    rw [← MeasureTheory.Lp.norm_fourier_eq w, ← hu, hu0, norm_zero]
  exact norm_eq_zero.1 hnorm

/-! ### The main theorem -/

/-- **The free Laplacian is essentially self-adjoint on the Schwartz space**, proved via
Plancherel's theorem: the Fourier transform is unitary on `L²(ℝ, ℂ)` and turns `-d²/dx²` into
multiplication by `4π²ξ²`, so the ranges of `T ± i` are dense and the basic criterion applies.
The statement records that the domain (the Schwartz space) is dense, that the operator is
symmetric, and that the graph of its adjoint is exactly the closure of its graph. -/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel :
    DenseRange (fun f : 𝓢(ℝ, ℂ) => toL2 f) ∧
      IsSymmetricGraph freeLaplacianGraph ∧
      IsEssentiallySelfAdjointGraph freeLaplacianGraph := by
  refine ⟨?_, isSymmetricGraph_freeLaplacianGraph, ?_⟩
  · have hdense := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume)
      ENNReal.ofNat_ne_top
    have heq : (fun f : 𝓢(ℝ, ℂ) => toL2 f)
        = fun f : 𝓢(ℝ, ℂ) => SchwartzMap.toLpCLM ℝ ℂ 2 volume f := by
      funext f
      simp [toL2, SchwartzMap.toLpCLM_apply]
    rw [heq]
    exact hdense
  · refine isEssentiallySelfAdjointGraph_of_range_dense _ isSymmetricGraph_freeLaplacianGraph
      (fun w hw => orthogonal_shift_eq_zero Complex.I (by simp) w hw) (fun w hw => ?_)
    refine orthogonal_shift_eq_zero (-Complex.I) (by simp) w fun p hp => ?_
    have h := hw p hp
    rwa [neg_smul, ← sub_eq_add_neg]

end Concrete

end Brockian.FreeLaplacianPlancherel

