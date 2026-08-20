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
