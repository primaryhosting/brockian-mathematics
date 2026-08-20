/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology
open scoped ComplexInnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Aux

theorem inner_rsmul_left (r : ℝ) (a b : H) : ⟪r • a, b⟫ = (r : ℂ) * ⟪a, b⟫ := by
  rw [← algebraMap_smul ℂ r a, inner_smul_left]; simp

theorem inner_rsmul_right (r : ℝ) (a b : H) : ⟪a, r • b⟫ = (r : ℂ) * ⟪a, b⟫ := by
  rw [← algebraMap_smul ℂ r b, inner_smul_right]; simp

theorem tendsto_neg_punctured : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_neg.tendsto (0:ℝ))
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

end Aux

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a family `U t` of unitaries (surjective linear isometries) with `U 0 = 1`,
`U (s + t) = U s ∘ U t`, and `t ↦ U t x` continuous for every `x`. -/
structure IsUnitaryGroup (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : Prop where
  zero : ∀ x, U 0 x = x
  add : ∀ s t x, U (s + t) x = U s (U t x)
  cont : ∀ x, Continuous fun t => U t x

/-- `HasGenerator U x y` says that `x` lies in the domain of the (Stone) generator `A` of the
one-parameter group `U` and that `A x = y`; i.e. `t ↦ U t x` is differentiable at `t = 0` with
derivative `i • y`, the normalization corresponding to `U t = exp (i t A)`. -/
def HasGenerator (U : ℝ → (H ≃ₗᵢ[ℂ] H)) (x y : H) : Prop :=
  Tendsto (fun t : ℝ => t⁻¹ • (U t x - x)) (𝓝[≠] (0 : ℝ)) (𝓝 (Complex.I • y))

section Basic

variable {U : ℝ → (H ≃ₗᵢ[ℂ] H)}

/-- Unitarity: the adjoint of `U t` is `U (-t)`. -/
theorem inner_apply_left (hU : IsUnitaryGroup U) (t : ℝ) (x y : H) :
    ⟪U t x, y⟫ = ⟪x, U (-t) y⟫ := by
  have h : U t (U (-t) y) = y := by rw [← hU.add, add_neg_cancel, hU.zero]
  calc ⟪U t x, y⟫ = ⟪U t x, U t (U (-t) y)⟫ := by rw [h]
    _ = ⟪x, U (-t) y⟫ := (U t).inner_map_map _ _

theorem hasGenerator_zero : HasGenerator U 0 0 := by
  unfold HasGenerator
  simp only [map_zero, sub_zero, smul_zero]
  exact tendsto_const_nhds

theorem hasGenerator_unique {x y₁ y₂ : H} (h₁ : HasGenerator U x y₁) (h₂ : HasGenerator U x y₂) :
    y₁ = y₂ :=
  smul_right_injective H Complex.I_ne_zero (tendsto_nhds_unique h₁ h₂)

theorem hasGenerator_add_smul {c : ℂ} {x₁ y₁ x₂ y₂ : H} (h₁ : HasGenerator U x₁ y₁)
    (h₂ : HasGenerator U x₂ y₂) : HasGenerator U (x₁ + c • x₂) (y₁ + c • y₂) := by
  have hsum := h₁.add (h₂.const_smul c)
  have heq : ∀ t : ℝ, t⁻¹ • (U t x₁ - x₁) + c • (t⁻¹ • (U t x₂ - x₂))
      = t⁻¹ • (U t (x₁ + c • x₂) - (x₁ + c • x₂)) := by
    intro t
    simp only [map_add, map_smul, smul_sub, smul_add]
    simp only [smul_comm c (t⁻¹ : ℝ)]
    abel
  have hval : Complex.I • y₁ + c • Complex.I • y₂ = Complex.I • (y₁ + c • y₂) := by
    rw [smul_add, smul_comm c Complex.I]
  rw [HasGenerator, ← hval]
  exact hsum.congr heq

/-- The generator is symmetric. -/
theorem hasGenerator_symmetric (hU : IsUnitaryGroup U) {x₁ y₁ x₂ y₂ : H}
    (h₁ : HasGenerator U x₁ y₁) (h₂ : HasGenerator U x₂ y₂) : ⟪y₁, x₂⟫ = ⟪x₁, y₂⟫ := by
  have hA : Tendsto (fun t : ℝ => ⟪t⁻¹ • (U t x₁ - x₁), x₂⟫) (𝓝[≠] (0:ℝ))
      (𝓝 ⟪Complex.I • y₁, x₂⟫) := h₁.inner tendsto_const_nhds
  have hB : Tendsto (fun t : ℝ => ⟪x₁, t⁻¹ • (U t x₂ - x₂)⟫) (𝓝[≠] (0:ℝ))
      (𝓝 ⟪x₁, Complex.I • y₂⟫) := tendsto_const_nhds.inner h₂
  have hB' := (hB.comp tendsto_neg_punctured).neg
  have heq : ∀ t : ℝ, ⟪t⁻¹ • (U t x₁ - x₁), x₂⟫
      = -((fun t : ℝ => ⟪x₁, t⁻¹ • (U t x₂ - x₂)⟫) ∘ (fun t : ℝ => -t)) t := by
    intro t
    simp only [Function.comp_apply, inner_rsmul_left, inner_rsmul_right, inner_sub_left,
      inner_sub_right, inv_neg, Complex.ofReal_neg, Complex.ofReal_inv]
    rw [inner_apply_left hU t x₁ x₂]
    ring
  have hlim : ⟪Complex.I • y₁, x₂⟫ = -⟪x₁, Complex.I • y₂⟫ :=
    tendsto_nhds_unique (hA.congr fun t => heq t) hB'
  rw [inner_smul_left, inner_smul_right] at hlim
  simp only [Complex.conj_I] at hlim
  exact mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) (a := -Complex.I)
    (b := ⟪y₁, x₂⟫) (c := ⟪x₁, y₂⟫) (by linear_combination hlim)

end Basic

section Resolvent

variable [CompleteSpace H] {U : ℝ → (H ≃ₗᵢ[ℂ] H)}

/-- Resolvent construction: for every `x` there is a `w` in the domain of the generator `A`
with `A w = i • (x - w)`, i.e. `(A + i) w = i • x`.  Here
`w = ∫_0^∞ e^{-t} U t x dt = (1 - i A)⁻¹ x`. -/
theorem exists_hasGenerator_add (hU : IsUnitaryGroup U) (x : H) :
    ∃ w : H, HasGenerator U w (Complex.I • (x - w)) := by
  set g : ℝ → H := fun u => Real.exp (-u) • U u x with hg
  have hc : Continuous g := ((Real.continuous_exp.comp continuous_neg).smul (hU.cont x))
  have hint : ∀ s : ℝ, IntegrableOn g (Ioi s) volume := by
    intro s
    refine Integrable.mono' (((exp_neg_integrableOn_Ioi s one_pos).mul_const ‖x‖))
      hc.aestronglyMeasurable.restrict ?_
    filter_upwards with u
    rw [hg, norm_smul]
    simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  set F : ℝ → H := fun s => ∫ u in Ioi s, g u with hF
  have hFU : ∀ s : ℝ, U s (F 0) = Real.exp s • F s := by
    intro s
    have h1 : U s (F 0) = ∫ u in Ioi (0:ℝ), U s (g u) :=
      ((U s).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hint 0)).symm
    have h2 : ∀ u : ℝ, U s (g u) = Real.exp s • g (s + u) := by
      intro u
      rw [hg]
      simp only [map_real_smul (U s) (U s).continuous, smul_smul]
      rw [← hU.add s u]
      congr 1
      rw [← Real.exp_add]
      ring_nf
    have h3 : ∫ u in Ioi (0:ℝ), g (s + u) = ∫ v in Ioi s, g v := by
      have := (measurePreserving_add_left (volume : Measure ℝ) s).setIntegral_preimage_emb
        (measurableEmbedding_addLeft s) g (Ioi s)
      simpa [Set.preimage, add_comm] using this
    rw [h1]
    simp only [h2]
    rw [integral_smul, h3]
  have hFsplit : ∀ s : ℝ, s ≤ 1 → F s = (∫ u in s..(1:ℝ), g u) + ∫ u in Ioi (1:ℝ), g u := by
    intro s hs
    have hsplit : Ioi s = Ioc s 1 ∪ Ioi 1 := by rw [Ioc_union_Ioi_eq_Ioi hs]
    rw [hF]
    simp only
    rw [hsplit, setIntegral_union (by simp [Set.disjoint_left])
      measurableSet_Ioi ((hint s).mono_set (fun a ha => ha.1)) (hint 1),
      intervalIntegral.integral_of_le hs]
  have hg0 : g 0 = x := by rw [hg]; simp [hU.zero]
  have hderiv : HasDerivAt F (-x) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (∫ u in s..(1:ℝ), g u) + ∫ u in Ioi (1:ℝ), g u) (-g 0) 0 :=
      (intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).add_const _
    rw [hg0] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)] with s hs
    exact hFsplit s (le_of_lt hs)
  refine ⟨F 0, ?_⟩
  have hlim1 : Tendsto (fun s : ℝ => (Real.exp s - 1) / s) (𝓝[≠] (0:ℝ)) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_exp 0)
    rw [Real.exp_zero] at h
    refine h.congr fun s => ?_
    simp [slope_def_field, div_eq_inv_mul]
  have hlim2 : Tendsto F (𝓝[≠] (0:ℝ)) (𝓝 (F 0)) :=
    hderiv.continuousAt.continuousWithinAt.tendsto
  have hlim3 : Tendsto (fun s : ℝ => s⁻¹ • (F s - F 0)) (𝓝[≠] (0:ℝ)) (𝓝 (-x)) := by
    refine (hasDerivAt_iff_tendsto_slope.mp hderiv).congr fun s => ?_
    simp [slope, vsub_eq_sub]
  have hmain : Tendsto (fun s : ℝ => ((Real.exp s - 1)/s) • F s + s⁻¹ • (F s - F 0))
      (𝓝[≠] (0:ℝ)) (𝓝 ((1:ℝ) • F 0 + -x)) := (hlim1.smul hlim2).add hlim3
  have hval : Complex.I • (Complex.I • (x - F 0)) = (1:ℝ) • F 0 + -x := by
    rw [smul_smul, Complex.I_mul_I]
    simp
    module
  rw [HasGenerator, hval]
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  rw [hFU s, div_eq_mul_inv, mul_comm, ← smul_smul, ← smul_add]
  congr 1
  module

/-- The mirrored resolvent: for every `x` there is a `w` in the domain with `A w = i • (w - x)`,
i.e. `(A - i) w = -i • x`. -/
theorem exists_hasGenerator_sub (hU : IsUnitaryGroup U) (x : H) :
    ∃ w : H, HasGenerator U w (Complex.I • (w - x)) := by
  have hV : IsUnitaryGroup (fun t => U (-t)) := by
    refine ⟨by simpa using hU.zero, ?_, fun x => (hU.cont x).comp continuous_neg⟩
    intro s t x
    show U (-(s + t)) x = U (-s) (U (-t) x)
    rw [neg_add]
    exact hU.add _ _ _
  obtain ⟨w, hw⟩ := exists_hasGenerator_add hV x
  refine ⟨w, ?_⟩
  have h := (hw.comp tendsto_neg_punctured).neg
  have heq : ∀ t : ℝ, -((fun t : ℝ => t⁻¹ • ((fun t => U (-t)) t w - w)) ∘ (fun t : ℝ => -t)) t
      = t⁻¹ • (U t w - w) := by
    intro t
    simp [inv_neg]
  have hval : -(Complex.I • (Complex.I • (x - w))) = Complex.I • (Complex.I • (w - x)) := by
    rw [smul_smul, smul_smul, Complex.I_mul_I]
    module
  rw [HasGenerator, ← hval]
  exact h.congr heq

end Resolvent

section Main

variable [CompleteSpace H] {U : ℝ → (H ≃ₗᵢ[ℂ] H)}

/-- `A + i` is surjective. -/
theorem surjective_add_I (hU : IsUnitaryGroup U) (v : H) :
    ∃ w y, HasGenerator U w y ∧ y + Complex.I • w = v := by
  obtain ⟨w, hw⟩ := exists_hasGenerator_add hU (-Complex.I • v)
  refine ⟨w, _, hw, ?_⟩
  rw [smul_sub, smul_smul]
  simp [Complex.I_mul_I]

/-- `A - i` is surjective. -/
theorem surjective_sub_I (hU : IsUnitaryGroup U) (v : H) :
    ∃ w y, HasGenerator U w y ∧ y - Complex.I • w = v := by
  obtain ⟨w, hw⟩ := exists_hasGenerator_sub hU (Complex.I • v)
  refine ⟨w, _, hw, ?_⟩
  rw [smul_sub, smul_smul]
  simp [Complex.I_mul_I]

/-- The domain of the generator, as a linear subspace. -/
def domain (U : ℝ → (H ≃ₗᵢ[ℂ] H)) : Submodule ℂ H where
  carrier := {x : H | ∃ y, HasGenerator U x y}
  add_mem' := by
    rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
    refine ⟨ya + (1 : ℂ) • yb, ?_⟩
    have := hasGenerator_add_smul (c := (1:ℂ)) ha hb
    rwa [one_smul] at this
  zero_mem' := ⟨0, hasGenerator_zero⟩
  smul_mem' := by
    rintro c a ⟨ya, ha⟩
    refine ⟨(0 : H) + c • ya, ?_⟩
    have := hasGenerator_add_smul (c := c) (hasGenerator_zero (U := U)) ha
    rwa [zero_add] at this

omit [CompleteSpace H] in
theorem mem_domain_iff {x : H} : x ∈ domain U ↔ ∃ y, HasGenerator U x y := Iff.rfl

/-- The domain of the generator is dense. -/
theorem dense_domain (hU : IsUnitaryGroup U) : Dense {x : H | ∃ y, HasGenerator U x y} := by
  have hD : Dense ((domain U : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro v hv
    have hv' : ∀ u ∈ domain U, ⟪u, v⟫ = 0 := (Submodule.mem_orthogonal _ v).mp hv
    obtain ⟨p, y, hp, hpe⟩ := surjective_add_I hU v
    have hpv : ⟪p, v⟫ = 0 := hv' p ⟨y, hp⟩
    have hsym : ⟪y, p⟫ = ⟪p, y⟫ := hasGenerator_symmetric hU hp hp
    have hvp : ⟪v, p⟫ = 0 := by
      rw [← inner_conj_symm, hpv, map_zero]
    rw [← hpe, inner_add_left, inner_smul_left, Complex.conj_I] at hvp
    have hc : starRingEnd ℂ ⟪y, p⟫ = ⟪y, p⟫ := by rw [inner_conj_symm, hsym]
    have hr : starRingEnd ℂ ⟪p, p⟫ = ⟪p, p⟫ := inner_conj_symm p p
    have hrz : (⟪p, p⟫ : ℂ) = 0 := by
      have h2 : starRingEnd ℂ (⟪y, p⟫ + -Complex.I * ⟪p, p⟫) = 0 := by rw [hvp, map_zero]
      rw [map_add, map_mul, map_neg, hc, hr, Complex.conj_I] at h2
      have h3 : (2 : ℂ) * Complex.I * ⟪p, p⟫ = 0 := by linear_combination h2 - hvp
      simpa [Complex.I_ne_zero] using h3
    have hp0 : p = 0 := inner_self_eq_zero.mp hrz
    have hy0 : y = 0 := by
      rw [hp0] at hp
      exact hasGenerator_unique hp hasGenerator_zero
    rw [← hpe, hp0, hy0, smul_zero, add_zero]
  exact hD

/-- Maximality: the adjoint of the generator is the generator itself. -/
theorem hasGenerator_of_adjoint (hU : IsUnitaryGroup U) (w z : H)
    (h : ∀ x y, HasGenerator U x y → ⟪y, w⟫ = ⟪x, z⟫) : HasGenerator U w z := by
  obtain ⟨u, yu, hu, hue⟩ := surjective_sub_I hU (z - Complex.I • w)
  have hzero : z - yu - Complex.I • w + Complex.I • u = 0 := by
    have h2 : z - Complex.I • w - (yu - Complex.I • u) = 0 := by rw [hue]; abel
    rw [← h2]; abel
  have key : ∀ x y : H, HasGenerator U x y → ⟪y + Complex.I • x, w - u⟫ = 0 := by
    intro x y hy
    have hz : ⟪y, w⟫ = ⟪x, z⟫ := h x y hy
    have hs : ⟪y, u⟫ = ⟪x, yu⟫ := hasGenerator_symmetric hU hy hu
    have hexp : ⟪x, z⟫ - ⟪x, yu⟫ - Complex.I * ⟪x, w⟫ + Complex.I * ⟪x, u⟫ = 0 := by
      have h3 : (⟪x, z - yu - Complex.I • w + Complex.I • u⟫ : ℂ) = 0 := by
        rw [hzero, inner_zero_right]
      simpa [inner_add_right, inner_sub_right, inner_smul_right] using h3
    simp only [inner_add_left, inner_sub_right, inner_smul_left, Complex.conj_I]
    linear_combination hz - hs + hexp
  have hwu : w = u := by
    obtain ⟨p, yp, hp, hpe⟩ := surjective_add_I hU (w - u)
    have h4 := key p yp hp
    rw [hpe] at h4
    exact sub_eq_zero.mp (inner_self_eq_zero.mp h4)
  have hyz : yu = z := by
    rw [hwu] at hzero
    have hz0 : z - yu = 0 := by simpa using hzero
    exact (sub_eq_zero.mp hz0).symm
  rw [← hwu] at hu
  rwa [hyz] at hu

/-- **Stone's theorem**: a strongly continuous one-parameter unitary group `U` on a complex
Hilbert space has a self-adjoint generator `A`, characterized by
`d/dt (U t x)|_{t=0} = i • A x` (so that formally `U t = exp (i t A)`).

Explicitly:
1. the generator is well defined as an operator (the derivative determines `A x` uniquely);
2. its domain is a linear subspace on which `A` acts linearly;
3. its domain is dense;
4. `A` is symmetric;
5. `A` is self-adjoint: any `w` such that `⟪A x, w⟫ = ⟪x, z⟫` for all `x` in the domain
   already lies in the domain, and `A w = z`. -/
theorem stone_generator {U : ℝ → (H ≃ₗᵢ[ℂ] H)} (hU : IsUnitaryGroup U) :
    (∀ x y₁ y₂, HasGenerator U x y₁ → HasGenerator U x y₂ → y₁ = y₂) ∧
    (∀ (c : ℂ) x₁ y₁ x₂ y₂, HasGenerator U x₁ y₁ → HasGenerator U x₂ y₂ →
        HasGenerator U (x₁ + c • x₂) (y₁ + c • y₂)) ∧
    Dense {x : H | ∃ y, HasGenerator U x y} ∧
    (∀ x₁ y₁ x₂ y₂, HasGenerator U x₁ y₁ → HasGenerator U x₂ y₂ → ⟪y₁, x₂⟫ = ⟪x₁, y₂⟫) ∧
    (∀ w z : H, (∀ x y, HasGenerator U x y → ⟪y, w⟫ = ⟪x, z⟫) → HasGenerator U w z) :=
  ⟨fun _ _ _ h₁ h₂ => hasGenerator_unique h₁ h₂,
   fun _ _ _ _ _ h₁ h₂ => hasGenerator_add_smul h₁ h₂,
   dense_domain hU,
   fun _ _ _ _ h₁ h₂ => hasGenerator_symmetric hU h₁ h₂,
   fun w z h => hasGenerator_of_adjoint hU w z h⟩

end Main

/-- Sanity check that the hypotheses are satisfiable: the constant group `U t = 1` is a strongly
continuous one-parameter unitary group, and its generator is the zero operator, defined on all
of `H`. -/
example : IsUnitaryGroup (fun _ : ℝ => (LinearIsometryEquiv.refl ℂ H)) ∧
    ∀ x : H, HasGenerator (fun _ : ℝ => (LinearIsometryEquiv.refl ℂ H)) x 0 := by
  refine ⟨⟨fun _ => rfl, fun _ _ _ => rfl, fun _ => continuous_const⟩, fun x => ?_⟩
  unfold HasGenerator
  simp

end QPhys

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

