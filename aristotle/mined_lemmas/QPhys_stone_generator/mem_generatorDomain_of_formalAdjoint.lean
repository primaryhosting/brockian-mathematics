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

set_option grind.warning false

/-!
# Stone's theorem: the generator of a strongly continuous one-parameter unitary group

We define the (skew-)generator of a strongly continuous one-parameter unitary group
`U : ℝ → H →L[ℂ] H` on a complex Hilbert space `H` as the unbounded operator
`A x = -i * (d/dt)|_{t=0} U t x`, with domain the set of vectors at which `t ↦ U t x`
is differentiable at `0`.

The main result `QPhys.stone_generator` states that this operator is densely defined and
self-adjoint, i.e. `(generator U)† = generator U`.
-/

namespace QPhys

open Filter Topology Complex
open scoped InnerProductSpace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  /-- `U 0` is the identity. -/
  map_zero : U 0 = 1
  /-- `U` is a one-parameter group. -/
  map_add : ∀ s t : ℝ, U (s + t) = (U s).comp (U t)
  /-- Each `U t` preserves the inner product. -/
  inner_map : ∀ (t : ℝ) (x y : H), ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ
  /-- `U` is strongly continuous. -/
  continuous_apply : ∀ x : H, Continuous fun t => U t x

namespace IsUnitaryGroup

variable {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U)
include hU


theorem mem_generatorDomain_of_formalAdjoint [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U)
    {y z : H} (hyz : ∀ u : (generator U).domain, ⟪z, (u : H)⟫_ℂ = ⟪y, generator U u⟫_ℂ) :
    ∃ h : y ∈ generatorDomain U, generator U ⟨y, h⟩ = z := by
  have hdense := dense_generatorDomain hU
  set w : H := Complex.I • z with hw
  -- Step 1: the weak orbit `s ↦ ⟪u, U s y⟫` is differentiable at `0`.
  have h0 : ∀ u : (generator U).domain,
      HasDerivAt (fun s : ℝ => ⟪(u : H), U s y⟫_ℂ) (⟪(u : H), w⟫_ℂ) 0 := by
    intro u
    have hg := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_generator_neg u)
    have t2 : Filter.Tendsto
        (fun h : ℝ => ⟪slope (fun t : ℝ => U (-t) (u : H)) 0 h, y⟫_ℂ) (𝓝[≠] (0 : ℝ))
        (𝓝 ⟪-(Complex.I • generator U u), y⟫_ℂ) := hg.inner tendsto_const_nhds
    have hfun : slope (fun s : ℝ => ⟪(u : H), U s y⟫_ℂ) 0
        = fun h : ℝ => ⟪slope (fun t : ℝ => U (-t) (u : H)) 0 h, y⟫_ℂ := by
      funext h
      have key : ⟪(u : H), U h y⟫_ℂ - ⟪(u : H), y⟫_ℂ = ⟪U (-h) (u : H) - (u : H), y⟫_ℂ := by
        rw [inner_sub_left, ← hU.inner_apply_right]
      simp only [slope, vsub_eq_sub, sub_zero, hU.apply_zero, neg_zero]
      simp [key, Complex.real_smul]
    have hval : ⟪(u : H), w⟫_ℂ = ⟪-(Complex.I • generator U u), y⟫_ℂ := by
      have hAu : ⟪(generator U u : H), y⟫_ℂ = ⟪(u : H), z⟫_ℂ := by
        rw [← inner_conj_symm, ← hyz u, inner_conj_symm]
      rw [hw, inner_smul_right, inner_neg_left, inner_smul_left, Complex.conj_I, hAu]
      ring
    rw [hasDerivAt_iff_tendsto_slope, hfun, hval]
    exact t2
  -- Step 2: differentiability of the weak orbit at every time.
  have hgen : ∀ (u : (generator U).domain) (t : ℝ),
      HasDerivAt (fun s : ℝ => ⟪(u : H), U s y⟫_ℂ) (⟪(u : H), U t w⟫_ℂ) t := by
    intro u t
    have hu' : U (-t) (u : H) ∈ (generator U).domain :=
      generatorDomain_invariant hU (-t) u.2
    have hfun : (fun s : ℝ => ⟪(u : H), U s y⟫_ℂ)
        = fun s : ℝ => ⟪U (-t) (u : H), U (s - t) y⟫_ℂ := by
      funext s
      rw [← hU.inner_map (-t) (u : H) (U s y), ← hU.apply_add, neg_add_eq_sub]
    have hv : ⟪(u : H), U t w⟫_ℂ = ⟪U (-t) (u : H), w⟫_ℂ := hU.inner_apply_right t (u : H) w
    have hstep : HasDerivAt (fun h : ℝ => ⟪U (-t) (u : H), U h y⟫_ℂ)
        (⟪U (-t) (u : H), w⟫_ℂ) (t - t) := by
      simpa using h0 ⟨U (-t) (u : H), hu'⟩
    rw [hfun, hv]
    exact HasDerivAt.comp_sub_const (f := fun h : ℝ => ⟪U (-t) (u : H), U h y⟫_ℂ) t t hstep
  -- Step 3: the fundamental theorem of calculus, weakly.
  have hFTC : ∀ (u : (generator U).domain) (t : ℝ),
      ⟪(u : H), U t y⟫_ℂ - ⟪(u : H), y⟫_ℂ = ∫ s in (0 : ℝ)..t, ⟪(u : H), U s w⟫_ℂ := by
    intro u t
    have hcont : Continuous fun s : ℝ => ⟪(u : H), U s w⟫_ℂ :=
      Continuous.inner continuous_const (hU.continuous_apply w)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => ⟪(u : H), U s y⟫_ℂ) (f' := fun s : ℝ => ⟪(u : H), U s w⟫_ℂ)
      (a := 0) (b := t) (fun s _ => hgen u s) (hcont.intervalIntegrable 0 t)
    rw [this]
    simp [hU.apply_zero]
  -- Step 4: the identity between vectors, by density.
  have hvec : ∀ t : ℝ, U t y - y = ∫ s in (0 : ℝ)..t, U s w := by
    intro t
    refine hdense.eq_of_inner_left ?_
    intro v
    have hcomm : (∫ s in (0 : ℝ)..t, ⟪(v : H), U s w⟫_ℂ)
        = ⟪(v : H), ∫ s in (0 : ℝ)..t, U s w⟫_ℂ :=
      (innerSL ℂ (v : H)).intervalIntegral_comp_comm (intervalIntegrable_orbit hU w 0 t)
    have hv : ⟪(v : H), U t y - y⟫_ℂ = ⟪(v : H), ∫ s in (0 : ℝ)..t, U s w⟫_ℂ := by
      rw [inner_sub_right, hFTC v t, hcomm]
    have := congrArg (starRingEnd ℂ) hv
    simpa only [inner_conj_symm] using this
  -- Step 5: conclude that `y` is in the domain, with `A y = z`.
  have hd : HasDerivAt (fun t : ℝ => U t y) w 0 := by
    have hG : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t, U s w) (U 0 w) 0 :=
      hasDerivAt_orbitIntegral hU w 0
    have hfun : (fun t : ℝ => U t y) = fun t : ℝ => (∫ s in (0 : ℝ)..t, U s w) + y := by
      funext t
      rw [← hvec t]
      abel
    rw [hfun]
    simpa [hU.apply_zero] using hG.add_const y
  refine ⟨hd.differentiableAt, ?_⟩
  show (-Complex.I) • deriv (fun t : ℝ => U t y) 0 = z
  rw [hd.deriv, hw, smul_smul]
  simp

/-- Every vector in the domain of the adjoint lies in the domain of the generator. -/
