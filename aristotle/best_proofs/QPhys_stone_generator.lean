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

theorem apply_add (s t : ℝ) (x : H) : U (s + t) x = U s (U t x) := by
  rw [hU.map_add]; rfl

theorem apply_zero (x : H) : U 0 x = x := by rw [hU.map_zero]; rfl

theorem apply_neg_apply (t : ℝ) (x : H) : U (-t) (U t x) = x := by
  rw [← hU.apply_add, neg_add_cancel, hU.apply_zero]

theorem apply_apply_neg (t : ℝ) (x : H) : U t (U (-t) x) = x := by
  rw [← hU.apply_add, add_neg_cancel, hU.apply_zero]

theorem inner_apply_left (t : ℝ) (x y : H) : ⟪U t x, y⟫_ℂ = ⟪x, U (-t) y⟫_ℂ := by
  conv_lhs => rw [← hU.apply_apply_neg t y, hU.inner_map]

theorem inner_apply_right (t : ℝ) (x y : H) : ⟪x, U t y⟫_ℂ = ⟪U (-t) x, y⟫_ℂ := by
  conv_lhs => rw [← hU.apply_apply_neg t x, hU.inner_map]

end IsUnitaryGroup

/-- The domain of the generator: vectors `x` such that `t ↦ U t x` is differentiable at `0`. -/
def generatorDomain (U : ℝ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x : H | DifferentiableAt ℝ (fun t : ℝ => U t x) 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_add] at *
    exact hx.add hy
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact differentiableAt_const _
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, map_smul] at *
    exact hx.const_smul c

theorem mem_generatorDomain_iff {U : ℝ → H →L[ℂ] H} {x : H} :
    x ∈ generatorDomain U ↔ DifferentiableAt ℝ (fun t : ℝ => U t x) 0 := Iff.rfl

/-- The generator `A` of a one-parameter unitary group `U`, so that (formally) `U t = exp (i t A)`.
It is the unbounded operator `A x = -i • (d/dt)|_{t=0} (U t x)`. -/
noncomputable def generator (U : ℝ → H →L[ℂ] H) : H →ₗ.[ℂ] H where
  domain := generatorDomain U
  toFun :=
    { toFun := fun x => (-Complex.I) • deriv (fun t : ℝ => U t (x : H)) 0
      map_add' := by
        intro x y
        have hx : DifferentiableAt ℝ (fun t : ℝ => U t (x : H)) 0 := x.2
        have hy : DifferentiableAt ℝ (fun t : ℝ => U t (y : H)) 0 := y.2
        have hF : HasDerivAt (fun t : ℝ => U t ((x : H) + (y : H)))
            (deriv (fun t : ℝ => U t (x : H)) 0 + deriv (fun t : ℝ => U t (y : H)) 0) 0 := by
          simpa only [map_add] using hx.hasDerivAt.add hy.hasDerivAt
        rw [Submodule.coe_add, hF.deriv, smul_add]
      map_smul' := by
        intro c x
        have hx : DifferentiableAt ℝ (fun t : ℝ => U t (x : H)) 0 := x.2
        have hF : HasDerivAt (fun t : ℝ => U t (c • (x : H)))
            (c • deriv (fun t : ℝ => U t (x : H)) 0) 0 := by
          simpa only [map_smul] using hx.hasDerivAt.const_smul c
        rw [RingHom.id_apply, Submodule.coe_smul_of_tower, hF.deriv, smul_comm] }

@[simp] theorem generator_domain (U : ℝ → H →L[ℂ] H) :
    (generator U).domain = generatorDomain U := rfl

theorem generator_apply (U : ℝ → H →L[ℂ] H) (x : (generator U).domain) :
    generator U x = (-Complex.I) • deriv (fun t : ℝ => U t (x : H)) 0 := rfl

/-- Composing with a continuous linear map preserves derivatives. -/
theorem hasDerivAt_clm (L : H →L[ℂ] H) {f : ℝ → H} {v : H} {t : ℝ} (h : HasDerivAt f v t) :
    HasDerivAt (fun s => L (f s)) (L v) t := by
  simpa using (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- For `x` in the domain, `t ↦ U t x` has derivative `i • A x` at `0`. -/
theorem hasDerivAt_generator {U : ℝ → H →L[ℂ] H} (x : (generator U).domain) :
    HasDerivAt (fun t : ℝ => U t (x : H)) (Complex.I • generator U x) 0 := by
  have hx : DifferentiableAt ℝ (fun t : ℝ => U t (x : H)) 0 := x.2
  have h : Complex.I • generator U x = deriv (fun t : ℝ => U t (x : H)) 0 := by
    rw [generator_apply, smul_smul]
    simp
  rw [h]
  exact hx.hasDerivAt

/-- The reflected orbit `t ↦ U (-t) x` has derivative `-(i • A x)` at `0`. -/
theorem hasDerivAt_generator_neg {U : ℝ → H →L[ℂ] H} (x : (generator U).domain) :
    HasDerivAt (fun t : ℝ => U (-t) (x : H)) (-(Complex.I • generator U x)) 0 := by
  have h0 : HasDerivAt (fun t : ℝ => U t (x : H)) (Complex.I • generator U x) (-(0 : ℝ)) := by
    simpa using hasDerivAt_generator x
  simpa [Function.comp] using h0.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))

/-- The domain of the generator is invariant under the group. -/
theorem generatorDomain_invariant {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (s : ℝ) {x : H}
    (hx : x ∈ generatorDomain U) : U s x ∈ generatorDomain U := by
  have hd : DifferentiableAt ℝ (fun t : ℝ => U t x) 0 := hx
  have h := hasDerivAt_clm (U s) hd.hasDerivAt
  have hfun : (fun t : ℝ => U s (U t x)) = fun t : ℝ => U t (U s x) := by
    funext t
    rw [← hU.apply_add, ← hU.apply_add, add_comm]
  rw [hfun] at h
  exact h.differentiableAt

/-- Orbits of a strongly continuous group are interval integrable. -/
theorem intervalIntegrable_orbit {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (x : H) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => U t x) MeasureTheory.volume a b :=
  (hU.continuous_apply x).intervalIntegrable a b

/-- The primitive `r ↦ ∫_0^r U t x dt` of an orbit has derivative `U s x` at `s`. -/
theorem hasDerivAt_orbitIntegral [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (x : H) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ t in (0 : ℝ)..r, U t x) (U s x) s :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_orbit hU x 0 s)
    ((hU.continuous_apply x).stronglyMeasurableAtFilter _ _)
    (hU.continuous_apply x).continuousAt

/-- The group translates the primitive of an orbit. -/
theorem orbitIntegral_group [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (x : H) (e s : ℝ) :
    U s (∫ t in (0 : ℝ)..e, U t x)
      = (∫ t in (0 : ℝ)..(e + s), U t x) - ∫ t in (0 : ℝ)..s, U t x := by
  have h1 : U s (∫ t in (0 : ℝ)..e, U t x) = ∫ t in (0 : ℝ)..e, U s (U t x) :=
    ((U s).intervalIntegral_comp_comm (intervalIntegrable_orbit hU x 0 e)).symm
  have h2 : (fun t : ℝ => U s (U t x)) = fun t : ℝ => U (t + s) x := by
    funext t
    rw [← hU.apply_add, add_comm]
  have h3 : (∫ t in (0 : ℝ)..e, U (t + s) x) = ∫ t in (0 + s)..(e + s), U t x :=
    intervalIntegral.integral_comp_add_right (fun t : ℝ => U t x) s
  have h4 : (∫ t in (0 : ℝ)..(e + s), U t x) - (∫ t in (0 : ℝ)..s, U t x)
      = ∫ t in s..(e + s), U t x :=
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_orbit hU x 0 (e + s))
      (intervalIntegrable_orbit hU x 0 s)
  rw [h1, h2, h3, h4, zero_add]

/-- Averages of an orbit over `[0, e]` belong to the domain of the generator. -/
theorem orbitIntegral_mem_generatorDomain [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) (x : H)
    (e : ℝ) : (∫ t in (0 : ℝ)..e, U t x) ∈ generatorDomain U := by
  have h1 : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..(e + s), U t x) (U e x) 0 :=
    HasDerivAt.comp_const_add e 0 (by simpa using hasDerivAt_orbitIntegral hU x e)
  have h2 : HasDerivAt (fun s : ℝ => ∫ t in (0 : ℝ)..s, U t x) (U 0 x) 0 :=
    hasDerivAt_orbitIntegral hU x 0
  have h3 : HasDerivAt (fun s : ℝ => U s (∫ t in (0 : ℝ)..e, U t x)) (U e x - U 0 x) 0 := by
    simpa only [orbitIntegral_group hU x e] using h1.sub h2
  exact h3.differentiableAt

/-- The domain of the generator is dense. -/
theorem dense_generatorDomain [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    Dense ((generator U).domain : Set H) := by
  intro x
  have hslope := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_orbitIntegral hU x 0)
  refine mem_closure_of_tendsto (b := 𝓝[≠] (0 : ℝ)) (by simpa [hU.apply_zero] using hslope) ?_
  filter_upwards with e
  have : slope (fun r : ℝ => ∫ t in (0 : ℝ)..r, U t x) 0 e
      = e⁻¹ • ∫ t in (0 : ℝ)..e, U t x := by
    simp [slope]
  rw [this]
  exact Submodule.smul_of_tower_mem _ _ (orbitIntegral_mem_generatorDomain hU x e)

/-- The generator is symmetric. -/
theorem generator_isFormalAdjoint {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    (generator U).IsFormalAdjoint (generator U) := by
  intro x y
  have hf := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_generator x)
  have hg := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_generator_neg y)
  have t1 : Filter.Tendsto
      (fun h : ℝ => ⟪slope (fun t : ℝ => U t (x : H)) 0 h, (y : H)⟫_ℂ) (𝓝[≠] (0 : ℝ))
      (𝓝 ⟪Complex.I • generator U x, (y : H)⟫_ℂ) := hf.inner tendsto_const_nhds
  have t2 : Filter.Tendsto
      (fun h : ℝ => ⟪(x : H), slope (fun t : ℝ => U (-t) (y : H)) 0 h⟫_ℂ) (𝓝[≠] (0 : ℝ))
      (𝓝 ⟪(x : H), -(Complex.I • generator U y)⟫_ℂ) := tendsto_const_nhds.inner hg
  have hfun : (fun h : ℝ => ⟪slope (fun t : ℝ => U t (x : H)) 0 h, (y : H)⟫_ℂ)
      = fun h : ℝ => ⟪(x : H), slope (fun t : ℝ => U (-t) (y : H)) 0 h⟫_ℂ := by
    funext h
    have key : ⟪U h (x : H) - (x : H), (y : H)⟫_ℂ = ⟪(x : H), U (-h) (y : H) - (y : H)⟫_ℂ := by
      rw [inner_sub_left, inner_sub_right, hU.inner_apply_left]
    simp only [slope, vsub_eq_sub, sub_zero, hU.apply_zero, neg_zero]
    simp [key]
  rw [hfun] at t1
  have heq := tendsto_nhds_unique t1 t2
  have h2 : ⟪(generator U x : H), (y : H)⟫_ℂ * Complex.I
      = Complex.I * ⟪(x : H), (generator U y : H)⟫_ℂ := by
    simpa [inner_smul_left, inner_smul_right, Complex.conj_I] using heq
  refine mul_left_cancel₀ Complex.I_ne_zero ?_
  rw [← h2]
  ring

/-- If `y` admits a formal adjoint value `z`, i.e. `⟪z, u⟫ = ⟪y, A u⟫` for all `u` in the domain
of the generator, then `y` itself lies in the domain of the generator and `A y = z`.
This is the heart of Stone's theorem. -/
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
theorem adjoint_le_generator [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    (generator U)† ≤ generator U := by
  have hdense := dense_generatorDomain hU
  have hfa := LinearPMap.adjoint_isFormalAdjoint (T := generator U) hdense
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨h, -⟩ := mem_generatorDomain_of_formalAdjoint hU (y := y)
      (z := (generator U)† ⟨y, hy⟩) (fun u => hfa ⟨y, hy⟩ u)
    exact h
  · rintro ⟨y, hy⟩ ⟨y', hy'⟩ (rfl : y = y')
    obtain ⟨h, heq⟩ := mem_generatorDomain_of_formalAdjoint hU (y := y)
      (z := (generator U)† ⟨y, hy⟩) (fun u => hfa ⟨y, hy⟩ u)
    exact heq.symm

/-- **Stone's theorem** (existence half): the generator of a strongly continuous one-parameter
unitary group is a densely defined self-adjoint operator. -/
theorem stone_generator [CompleteSpace H] {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    Dense ((generator U).domain : Set H) ∧ (generator U)† = generator U := by
  refine ⟨dense_generatorDomain hU, le_antisymm (adjoint_le_generator hU) ?_⟩
  exact (generator_isFormalAdjoint hU).le_adjoint (dense_generatorDomain hU)

/-!
### A worked example

The phase group `U t z = exp (i t) * z` on `ℂ` is a strongly continuous one-parameter unitary
group whose generator is the identity operator; this confirms that the hypotheses of
`stone_generator` are satisfiable and fixes the sign convention `U t = exp (i t A)`.
-/

/-- The phase group `t ↦ (z ↦ exp (i t) z)` on `ℂ`. -/
noncomputable def phaseGroup (t : ℝ) : ℂ →L[ℂ] ℂ :=
  Complex.exp (t * Complex.I) • ContinuousLinearMap.id ℂ ℂ

theorem isUnitaryGroup_phaseGroup : IsUnitaryGroup phaseGroup where
  map_zero := by
    ext
    simp [phaseGroup]
  map_add s t := by
    ext
    simp only [phaseGroup, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  inner_map t x y := by
    have h : Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-((t : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add]; simp
    simp only [phaseGroup, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      RCLike.inner_apply, smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_I,
      Complex.conj_ofReal, mul_neg]
    calc Complex.exp ((t : ℂ) * Complex.I) * y
            * (Complex.exp (-((t : ℂ) * Complex.I)) * (starRingEnd ℂ) x)
        = (Complex.exp ((t : ℂ) * Complex.I) * Complex.exp (-((t : ℂ) * Complex.I)))
            * (y * (starRingEnd ℂ) x) := by ring
      _ = y * (starRingEnd ℂ) x := by rw [h, one_mul]
  continuous_apply x := by
    unfold phaseGroup
    fun_prop

theorem hasDerivAt_phaseGroup (x : ℂ) :
    HasDerivAt (fun t : ℝ => phaseGroup t x) (Complex.I * x) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I
  simpa [phaseGroup] using (h1.cexp).mul_const x

theorem mem_generatorDomain_phaseGroup (x : ℂ) : x ∈ generatorDomain phaseGroup :=
  (hasDerivAt_phaseGroup x).differentiableAt

/-- The generator of the phase group is the identity operator. -/
theorem generator_phaseGroup (x : ℂ) :
    generator phaseGroup ⟨x, mem_generatorDomain_phaseGroup x⟩ = x := by
  show (-Complex.I) • deriv (fun t : ℝ => phaseGroup t x) 0 = x
  rw [(hasDerivAt_phaseGroup x).deriv, smul_eq_mul, ← mul_assoc]
  simp

end QPhys

