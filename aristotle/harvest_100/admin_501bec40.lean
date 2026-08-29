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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with unbounded operators on a complex inner product space `H`, presented as linear maps
`T : D →ₗ[ℂ] H` out of a submodule `D` (the operator domain).

For a densely defined symmetric operator `T`, essential self-adjointness is equivalent to the
symmetry of the adjoint `T†` (equivalently: `T† = T††`, i.e. the closure `T̄ = T††` is
self-adjoint).  Since the adjoint of an unbounded operator is only defined on the set of vectors
`y` for which a representing vector `z` exists, we encode `z = T† y` through the relation
`IsAdjointPair T y z`, and encode symmetry of `T†` as `AdjointIsSymmetric T`.  This avoids any
use of choice and is exactly the classical criterion.

The main result is the (bounded) Kato–Rellich theorem in the concrete Schrödinger setting: on
`L²(ℝ)`, if the kinetic part `T` (e.g. `-d²/dx²` on a core such as `Cc^∞` or the Schwartz space)
is essentially self-adjoint, then adding a potential `V` of *weak regularity* — merely a.e. measurable
and essentially bounded, with no continuity or differentiability assumed — preserves essential
self-adjointness. In particular the deficiency spaces of the Schrödinger operator `-Δ + V` are
trivial, i.e. its deficiency indices vanish (Weyl's deficiency-index criterion).
-/

open MeasureTheory

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `IsAdjointPair T y z` says that `z` represents the adjoint `T† y`, i.e.
`⟪T x, y⟫ = ⟪x, z⟫` for all `x` in the domain of `T`. -/
def IsAdjointPair {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) (y z : H) : Prop :=
  ∀ x : D, inner ℂ (T x) y = inner ℂ (x : H) z

/-- `T` is symmetric on its domain: `⟪T x, y⟫ = ⟪x, T y⟫` for `x, y` in the domain. -/
def IsSymmetricOn {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) : Prop :=
  ∀ x y : D, inner ℂ (T x) (y : H) = inner ℂ (x : H) (T y)

/-- The adjoint `T†` of `T` is symmetric: whenever `z₁ = T† y₁` and `z₂ = T† y₂`, we have
`⟪T† y₁, y₂⟫ = ⟪y₁, T† y₂⟫`. -/
def AdjointIsSymmetric {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) : Prop :=
  ∀ y₁ z₁ y₂ z₂ : H, IsAdjointPair T y₁ z₁ → IsAdjointPair T y₂ z₂ →
    inner ℂ z₁ y₂ = inner ℂ y₁ z₂

/-- Essential self-adjointness of a densely defined operator `T`, in the classical formulation:
`T` is densely defined and symmetric, and its adjoint is symmetric (equivalently, the closure of
`T` is self-adjoint). -/
structure EssentiallySelfAdjoint {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) : Prop where
  denseDomain : Dense (D : Set H)
  symmetric : IsSymmetricOn T
  adjointSymmetric : AdjointIsSymmetric T

/-- Adding an everywhere-defined symmetric (in particular bounded self-adjoint) operator `B`
preserves essential self-adjointness: this is the bounded case of the Kato–Rellich theorem. -/
theorem essentiallySelfAdjoint_add_symmetric
    {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) (hT : EssentiallySelfAdjoint T)
    (B : H →ₗ[ℂ] H) (hB : ∀ x y : H, inner ℂ (B x) y = inner ℂ x (B y)) :
    EssentiallySelfAdjoint (T + B ∘ₗ D.subtype) := by
  refine ⟨hT.denseDomain, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [inner_add_left, inner_add_right, hT.symmetric x y, hB (x : H) (y : H)]
  · intro y₁ z₁ y₂ z₂ h₁ h₂
    have k₁ : IsAdjointPair T y₁ (z₁ - B y₁) := by
      intro x
      have hx := h₁ x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        inner_add_left] at hx
      rw [hB (x : H) y₁] at hx
      rw [inner_sub_right]
      linear_combination hx
    have k₂ : IsAdjointPair T y₂ (z₂ - B y₂) := by
      intro x
      have hx := h₂ x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        inner_add_left] at hx
      rw [hB (x : H) y₂] at hx
      rw [inner_sub_right]
      linear_combination hx
    have hsym := hT.adjointSymmetric y₁ (z₁ - B y₁) y₂ (z₂ - B y₂) k₁ k₂
    rw [inner_sub_left, inner_sub_right, hB y₁ y₂] at hsym
    linear_combination hsym

/-- The deficiency spaces of an essentially self-adjoint operator are trivial: for non-real `c`,
no nonzero vector is orthogonal to the range of `T - c`. -/
theorem deficiency_eq_zero {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (hT : EssentiallySelfAdjoint T) {c : ℂ} (hc : c.im ≠ 0) {v : H}
    (hv : ∀ x : D, inner ℂ (T x - c • (x : H)) v = 0) : v = 0 := by
  have hpair : IsAdjointPair T v ((starRingEnd ℂ) c • v) := by
    intro x
    have hx := hv x
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at hx
    rw [hx, inner_smul_right]
  have hsym := hT.adjointSymmetric v ((starRingEnd ℂ) c • v) v ((starRingEnd ℂ) c • v)
    hpair hpair
  rw [inner_smul_left, inner_smul_right, RingHomCompTriple.comp_apply, RingHom.id_apply] at hsym
  have hcc : c - (starRingEnd ℂ) c ≠ 0 := by
    intro h
    apply hc
    have : (c - (starRingEnd ℂ) c).im = 0 := by rw [h]; simp
    simp [Complex.sub_im, Complex.conj_im] at this
    linarith
  have hzero : (inner ℂ v v : ℂ) = 0 := by
    have : (c - (starRingEnd ℂ) c) * (inner ℂ v v : ℂ) = 0 := by linear_combination hsym
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hcc
    · exact h
  simpa using inner_self_eq_zero.mp hzero

/-- Weyl's deficiency criterion in the form we get here: for an essentially self-adjoint operator
`T` and non-real `c`, the range of `T - c` is dense. -/
theorem dense_range_sub_smul [CompleteSpace H] {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (hT : EssentiallySelfAdjoint T) {c : ℂ} (hc : c.im ≠ 0) :
    Dense (Set.range fun x : D => T x - c • (x : H)) := by
  set K : Submodule ℂ H := LinearMap.range (T - c • D.subtype) with hK
  have hrange : (K : Set H) = Set.range fun x : D => T x - c • (x : H) := by
    ext y
    simp [hK, LinearMap.mem_range, LinearMap.sub_apply]
  have horth : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    refine deficiency_eq_zero hT hc (fun x => ?_)
    refine hv _ ?_
    exact ⟨x, by simp [LinearMap.sub_apply]⟩
  have hclos : K.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr horth
  have : Dense (K : Set H) := by
    rw [← Submodule.dense_iff_topologicalClosure_eq_top] at hclos
    exact hclos
  rwa [hrange] at this

/-- Sanity check that the hypotheses above are satisfiable: the zero operator on the whole space
is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_zero :
    EssentiallySelfAdjoint (0 : (⊤ : Submodule ℂ H) →ₗ[ℂ] H) := by
  refine ⟨by simp, fun x y => by simp, ?_⟩
  intro y₁ z₁ y₂ z₂ h₁ h₂
  have hz : ∀ z : H, IsAdjointPair (0 : (⊤ : Submodule ℂ H) →ₗ[ℂ] H) y₁ z → z = 0 := by
    intro z hz
    have := hz ⟨z, Submodule.mem_top⟩
    simp only [LinearMap.zero_apply, inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  have hz' : ∀ z : H, IsAdjointPair (0 : (⊤ : Submodule ℂ H) →ₗ[ℂ] H) y₂ z → z = 0 := by
    intro z hz
    have := hz ⟨z, Submodule.mem_top⟩
    simp only [LinearMap.zero_apply, inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  rw [hz z₁ h₁, hz' z₂ h₂]
  simp

end Abstract

section Potential

variable (V : ℝ → ℝ) (hV : AEStronglyMeasurable V volume) (C : ℝ)
  (hVb : ∀ᵐ x : ℝ, |V x| ≤ C)

include hV hVb in
/-- A bounded measurable potential multiplies `L²`-functions into `L²`-functions. -/
theorem memLp_mul_potential (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun x => (V x : ℂ) * (f : ℝ → ℂ) x) 2 volume := by
  refine MemLp.of_le ((Lp.memLp f).const_mul (C : ℂ)) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hV).mul
      (Lp.aestronglyMeasurable f)
  · filter_upwards [hVb] with x hx
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (norm_nonneg _)

/-- The potential term of a Schrödinger operator: multiplication by a bounded measurable
real-valued function `V`, as an everywhere-defined operator on `L²(ℝ)`. -/
def mulPotential : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := (memLp_mul_potential V hV C hVb f).toLp _
  map_add' f g := by
    rw [Lp.ext_iff]
    filter_upwards [(memLp_mul_potential V hV C hVb (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_mul_potential V hV C hVb f).toLp _)
        ((memLp_mul_potential V hV C hVb g).toLp _),
      (memLp_mul_potential V hV C hVb f).coeFn_toLp,
      (memLp_mul_potential V hV C hVb g).coeFn_toLp, Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply]
    ring
  map_smul' c f := by
    rw [Lp.ext_iff]
    filter_upwards [(memLp_mul_potential V hV C hVb (c • f)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_mul_potential V hV C hVb f).toLp _),
      (memLp_mul_potential V hV C hVb f).coeFn_toLp, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
    ring

include hV hVb in
/-- Multiplication by a real-valued bounded measurable function is a symmetric operator. -/
theorem mulPotential_symmetric (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ (mulPotential V hV C hVb f) g = inner ℂ f (mulPotential V hV C hVb g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_mul_potential V hV C hVb f).coeFn_toLp,
    (memLp_mul_potential V hV C hVb g).coeFn_toLp] with x h1 h2
  simp only [mulPotential, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2 ⊢
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply']
  simp only [map_mul, Complex.conj_ofReal]
  ring

end Potential

/-- **Essential self-adjointness of Schrödinger operators with a weakly regular potential.**

Let `T` be the kinetic part of a Schrödinger operator on `L²(ℝ)` (e.g. `-d²/dx²`), defined on a
core `D` on which it is essentially self-adjoint, and let `V : ℝ → ℝ` be a potential of *weak
regularity*: merely measurable and essentially bounded (`|V x| ≤ C` for a.e. `x`), with no continuity, differentiability
or ODE-regularity assumption.  Then the Schrödinger operator `T + V` is essentially self-adjoint
on the same core `D`. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity
    {D : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (T : D →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ)) (hT : EssentiallySelfAdjoint T)
    (V : ℝ → ℝ) (hV : AEStronglyMeasurable V volume) {C : ℝ} (hVb : ∀ᵐ x : ℝ, |V x| ≤ C) :
    EssentiallySelfAdjoint (T + (mulPotential V hV C hVb) ∘ₗ D.subtype) :=
  essentiallySelfAdjoint_add_symmetric T hT _ (mulPotential_symmetric V hV C hVb)

/-- The deficiency spaces of the Schrödinger operator `T + V` with a weakly regular potential are
trivial: for every non-real `c`, the range of `T + V - c` is dense in `L²(ℝ)`. -/
theorem schrodinger_dense_range_of_weakRegularity
    {D : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (T : D →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ)) (hT : EssentiallySelfAdjoint T)
    (V : ℝ → ℝ) (hV : AEStronglyMeasurable V volume) {C : ℝ} (hVb : ∀ᵐ x : ℝ, |V x| ≤ C)
    {c : ℂ} (hc : c.im ≠ 0) :
    Dense (Set.range fun x : D =>
      (T + (mulPotential V hV C hVb) ∘ₗ D.subtype) x - c • (x : Lp ℂ 2 (volume : Measure ℝ))) :=
  dense_range_sub_smul
    (schrodinger_essentiallySelfAdjoint_of_weakRegularity T hT V hV hVb) hc

/-- Unconditional special case: the potential term alone, i.e. multiplication by a weakly regular
(a.e. measurable, essentially bounded, real-valued) function, is essentially self-adjoint on all
of `L²(ℝ)`. -/
theorem mulPotential_essentiallySelfAdjoint
    (V : ℝ → ℝ) (hV : AEStronglyMeasurable V volume) {C : ℝ} (hVb : ∀ᵐ x : ℝ, |V x| ≤ C) :
    EssentiallySelfAdjoint
      ((0 : (⊤ : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) →ₗ[ℂ]
          Lp ℂ 2 (volume : Measure ℝ)) +
        (mulPotential V hV C hVb) ∘ₗ (⊤ : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))).subtype) :=
  schrodinger_essentiallySelfAdjoint_of_weakRegularity _ essentiallySelfAdjoint_zero V hV hVb

end Brockian.Weyl.DeficiencyODE

end

