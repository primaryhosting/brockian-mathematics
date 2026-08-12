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

/-!
# Stone's theorem

A strongly continuous one-parameter unitary group `U : ℝ → (H →L[ℂ] H)` on a complex Hilbert
space `H` has a self-adjoint (in general unbounded) generator `A`, characterized by
`d/dt (U t x) |_{t=0} = i • A x`.
-/

namespace QPhys

open scoped InnerProductSpace
open Complex (I)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → (H →L[ℂ] H)) : Prop where
  /-- Each `U t` is a unitary operator. -/
  mem_unitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)
  /-- The group law. -/
  map_add : ∀ s t : ℝ, U (s + t) = U s * U t
  /-- Strong continuity. -/
  strong_continuous : ∀ x : H, Continuous fun t => U t x

namespace IsUnitaryGroup

variable {U : ℝ → (H →L[ℂ] H)} (hU : IsUnitaryGroup U)
include hU

theorem inner_map_map (t : ℝ) (x y : H) : ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ :=
  ContinuousLinearMap.inner_map_map_of_mem_unitary (hU.mem_unitary t) x y

theorem norm_map (t : ℝ) (x : H) : ‖U t x‖ = ‖x‖ := by
  have h := hU.inner_map_map t x x
  have : (‖U t x‖ : ℝ) ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    exact_mod_cast congrArg Complex.re h
  have h1 : (0:ℝ) ≤ ‖U t x‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
  nlinarith [this]

theorem apply_zero : U 0 = 1 := by
  have h : U 0 * U 0 = U 0 := by
    have := hU.map_add 0 0
    simpa using this.symm
  have hs' : star (U 0) * U 0 = 1 := Unitary.star_mul_self_of_mem (hU.mem_unitary 0)
  calc U 0 = (star (U 0) * U 0) * U 0 := by rw [hs', one_mul]
    _ = star (U 0) * (U 0 * U 0) := by rw [mul_assoc]
    _ = star (U 0) * U 0 := by rw [h]
    _ = 1 := hs'

theorem left_inv (t : ℝ) (x : H) : U (-t) (U t x) = x := by
  have : U (-t) * U t = U 0 := by rw [← hU.map_add]; ring_nf
  have h2 : U (-t) * U t = 1 := by rw [this, hU.apply_zero]
  calc U (-t) (U t x) = (U (-t) * U t) x := rfl
    _ = x := by rw [h2]; rfl

theorem right_inv (t : ℝ) (x : H) : U t (U (-t) x) = x := by
  have := hU.left_inv (-t) x
  simpa using this

theorem inner_left (t : ℝ) (x y : H) : ⟪U t x, y⟫_ℂ = ⟪x, U (-t) y⟫_ℂ := by
  conv_lhs => rw [← hU.right_inv t y]
  exact hU.inner_map_map t x (U (-t) y)

end IsUnitaryGroup

/-! ### The generator -/

/-- The graph of the generator: pairs `(x, y)` such that `t ↦ U t x` is differentiable at `0`
with derivative `i • y`. -/
def genGraph (U : ℝ → (H →L[ℂ] H)) : Submodule ℂ (H × H) where
  carrier := {p : H × H | HasDerivAt (fun t => U t p.1) (I • p.2) 0}
  add_mem' := by
    intro a b ha hb
    have := ha.add hb
    simpa [Set.mem_setOf_eq, map_add, smul_add] using this
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, map_zero, smul_zero]
    simpa using (hasDerivAt_const (0:ℝ) (0:H))
  smul_mem' := by
    intro c a ha
    have := ha.const_smul (c : ℂ)
    have hfun : (fun t => U t ((c • a).1)) = (c • fun t => U t a.1) := by
      funext t; simp [Prod.smul_fst]
    rw [Set.mem_setOf_eq, hfun]
    simpa [smul_comm c I] using this

omit [CompleteSpace H] in
theorem mem_genGraph_iff (U : ℝ → (H →L[ℂ] H)) (p : H × H) :
    p ∈ genGraph U ↔ HasDerivAt (fun t => U t p.1) (I • p.2) 0 := Iff.rfl

omit [CompleteSpace H] in
theorem genGraph_fst_eq_zero (U : ℝ → (H →L[ℂ] H)) :
    ∀ p ∈ genGraph U, p.1 = 0 → p.2 = 0 := by
  intro p hp h1
  rw [mem_genGraph_iff] at hp
  rw [h1] at hp
  have hzero : HasDerivAt (fun _ : ℝ => U 0 0) (0 : H) 0 := by
    simpa using (hasDerivAt_const (0:ℝ) (U 0 0))
  have hp' : HasDerivAt (fun _ : ℝ => (0:H)) (I • p.2) 0 := by
    simpa using hp
  have : I • p.2 = 0 := by
    have h0 : HasDerivAt (fun _ : ℝ => (0:H)) (0:H) 0 := by
      simpa using (hasDerivAt_const (0:ℝ) (0:H))
    exact hp'.unique h0
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact (smul_eq_zero.mp this).resolve_left hI

/-- The generator of a one-parameter unitary group, as an unbounded (partially defined)
operator. -/
noncomputable def generator (U : ℝ → (H →L[ℂ] H)) : H →ₗ.[ℂ] H :=
  (genGraph U).toLinearPMap

omit [CompleteSpace H] in
theorem generator_domain (U : ℝ → (H →L[ℂ] H)) :
    (generator U).domain = (genGraph U).map (LinearMap.fst ℂ H H) :=
  Submodule.toLinearPMap_domain _

omit [CompleteSpace H] in
theorem mem_generator_domain_iff (U : ℝ → (H →L[ℂ] H)) (x : H) :
    x ∈ (generator U).domain ↔ ∃ y : H, HasDerivAt (fun t => U t x) (I • y) 0 := by
  rw [generator_domain]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨y, hy⟩
    exact ⟨(x, y), hy, rfl⟩

omit [CompleteSpace H] in
theorem mem_generator_domain {U : ℝ → (H →L[ℂ] H)} {x y : H}
    (h : HasDerivAt (fun t => U t x) (I • y) 0) : x ∈ (generator U).domain :=
  (mem_generator_domain_iff U x).2 ⟨y, h⟩

omit [CompleteSpace H] in
/-- Defining property of the generator. -/
theorem hasDerivAt_generator (U : ℝ → (H →L[ℂ] H)) (x : (generator U).domain) :
    HasDerivAt (fun t => U t (x : H)) (I • generator U x) 0 := by
  have h := Submodule.mem_graph_toLinearPMap (genGraph_fst_eq_zero U)
    (⟨(x : H), by rw [← generator_domain]; exact x.2⟩ :
      ((genGraph U).map (LinearMap.fst ℂ H H)))
  exact h

omit [CompleteSpace H] in
theorem generator_apply_eq {U : ℝ → (H →L[ℂ] H)} {x y : H} (hx : x ∈ (generator U).domain)
    (h : HasDerivAt (fun t => U t x) (I • y) 0) : generator U ⟨x, hx⟩ = y := by
  have h1 := hasDerivAt_generator U ⟨x, hx⟩
  have : I • generator U ⟨x, hx⟩ = I • y := h1.unique h
  exact smul_right_injective H Complex.I_ne_zero this

omit [CompleteSpace H] in
/-- Chain rule for a continuous linear map composed with a curve. -/
theorem clm_hasDerivAt (L : H →L[ℂ] H) {f : ℝ → H} {a : H} {t : ℝ} (h : HasDerivAt f a t) :
    HasDerivAt (fun s : ℝ => L (f s)) (L a) t :=
  (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- Solutions of `g' = r g` are exponentials. -/
theorem eq_exp_mul_of_hasDerivAt {g : ℝ → ℂ} (r : ℝ)
    (hg : ∀ t : ℝ, HasDerivAt g ((r : ℂ) * g t) t) (t : ℝ) :
    g t = Complex.exp ((r : ℂ) * t) * g 0 := by
  set G : ℝ → ℂ := fun t => Complex.exp (-(r : ℂ) * t) * g t with hGdef
  have hofReal : ∀ u : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ)) 1 u := by
    intro u
    simpa using (Complex.ofRealCLM.hasDerivAt (x := u))
  have hG : ∀ u : ℝ, HasDerivAt G 0 u := by
    intro u
    have h1 : HasDerivAt (fun s : ℝ => -(r : ℂ) * (s : ℂ)) (-(r : ℂ)) u := by
      simpa using (hofReal u).const_mul (-(r : ℂ))
    have h2 : HasDerivAt (fun s : ℝ => Complex.exp (-(r : ℂ) * (s : ℂ)))
        (Complex.exp (-(r : ℂ) * (u : ℂ)) * (-(r : ℂ))) u := h1.cexp
    have h4 : HasDerivAt (fun s : ℝ => Complex.exp (-(r : ℂ) * (s : ℂ)) * g s)
        (Complex.exp (-(r : ℂ) * (u : ℂ)) * (-(r : ℂ)) * g u
          + Complex.exp (-(r : ℂ) * (u : ℂ)) * ((r : ℂ) * g u)) u := h2.mul (hg u)
    rw [hGdef]
    convert h4 using 1
    ring
  have hdiff : Differentiable ℝ G := fun u => (hG u).differentiableAt
  have hfd : ∀ u : ℝ, fderiv ℝ G u = 0 := by
    intro u
    have := (hG u).hasFDerivAt.fderiv
    simpa using this
  have hconst : G t = G 0 := is_const_of_fderiv_eq_zero hdiff hfd t 0
  have hG0 : G 0 = g 0 := by simp [hGdef]
  rw [hG0] at hconst
  have hkey : Complex.exp (-(r : ℂ) * t) * g t = g 0 := hconst
  calc g t = Complex.exp ((r : ℂ) * t) * (Complex.exp (-(r : ℂ) * t) * g t) := by
        rw [← mul_assoc, ← Complex.exp_add]
        norm_num
    _ = Complex.exp ((r : ℂ) * t) * g 0 := by rw [hkey]

/-! ### Analytic properties -/

section Analysis

variable {U : ℝ → (H →L[ℂ] H)} (hU : IsUnitaryGroup U)
include hU

/-- For `x` in the domain of the generator, `t ↦ U t x` is differentiable everywhere. -/
theorem hasDerivAt_comp_left (x : (generator U).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U s (U t (x : H))) (I • U t (generator U x)) 0 := by
  have h0 := hasDerivAt_generator U x
  have h1 : HasDerivAt (fun s : ℝ => U t (U s (x : H))) (U t (I • generator U x)) 0 :=
    clm_hasDerivAt (U t) h0
  have hcomm : (fun s : ℝ => U t (U s (x : H))) = fun s : ℝ => U s (U t (x : H)) := by
    funext s
    have h2 : U t * U s = U s * U t := by
      rw [← hU.map_add, ← hU.map_add, add_comm]
    have := congrArg (fun L : H →L[ℂ] H => L (x : H)) h2
    exact this
  rw [hcomm] at h1
  simpa [map_smul] using h1

theorem apply_mem_domain (x : (generator U).domain) (t : ℝ) :
    U t (x : H) ∈ (generator U).domain :=
  mem_generator_domain (hasDerivAt_comp_left hU x t)

theorem generator_comm (x : (generator U).domain) (t : ℝ) :
    generator U ⟨U t (x : H), apply_mem_domain hU x t⟩ = U t (generator U x) :=
  generator_apply_eq _ (hasDerivAt_comp_left hU x t)

/-- For `x` in the domain of the generator, `t ↦ U t x` is differentiable everywhere. -/
theorem hasDerivAt_of_mem_domain (x : (generator U).domain) (t : ℝ) :
    HasDerivAt (fun s => U s (x : H)) (I • U t (generator U x)) t := by
  have h1 : HasDerivAt (fun s : ℝ => U t (U s (x : H))) (U t (I • generator U x)) 0 :=
    clm_hasDerivAt (U t) (hasDerivAt_generator U x)
  have h2 : HasDerivAt (fun s : ℝ => s - t) (1 : ℝ) t := by
    simpa using (hasDerivAt_id t).sub_const t
  have h3 : HasDerivAt ((fun s : ℝ => U t (U s (x : H))) ∘ fun s : ℝ => s - t)
      ((1 : ℝ) • U t (I • generator U x)) t := by
    apply HasDerivAt.scomp t (by simpa using h1) h2
  have hfun : ((fun s : ℝ => U t (U s (x : H))) ∘ fun s : ℝ => s - t)
      = fun s : ℝ => U s (x : H) := by
    funext s
    have h4 : U t * U (s - t) = U s := by
      rw [← hU.map_add]; ring_nf
    have := congrArg (fun L : H →L[ℂ] H => L (x : H)) h4
    exact this
  rw [hfun] at h3
  simpa [map_smul] using h3

/-- The curve `s ↦ U s v` is continuous. -/
theorem continuous_apply (v : H) : Continuous fun s : ℝ => U s v := hU.strong_continuous v

theorem intervalIntegrable_apply (v : H) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => U s v) MeasureTheory.volume a b :=
  (continuous_apply hU v).intervalIntegrable a b

/-- The fundamental theorem of calculus for the group. -/
theorem integral_formula (x : (generator U).domain) (t : ℝ) :
    (I : ℂ) • (∫ s in (0:ℝ)..t, U s (generator U x)) = U t (x : H) - (x : H) := by
  have hint : IntervalIntegrable (fun s : ℝ => (I : ℂ) • U s (generator U x))
      MeasureTheory.volume 0 t :=
    ((continuous_apply hU (generator U x)).const_smul (I : ℂ)).intervalIntegrable 0 t
  have hFTC : ((∫ s in (0:ℝ)..t, (I : ℂ) • U s (generator U x)))
      = (fun s : ℝ => U s (x : H)) t - (fun s : ℝ => U s (x : H)) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_of_mem_domain hU x s) hint
  rw [intervalIntegral.integral_smul] at hFTC
  rw [hFTC]
  simp [hU.apply_zero]

/-- If the integrated form of the equation holds, then `x` is in the domain with `A x = z`. -/
theorem mem_domain_of_integral_eq (x z : H)
    (h : ∀ t : ℝ, U t x - x = (I : ℂ) • ∫ s in (0:ℝ)..t, U s z) :
    ∃ hx : x ∈ (generator U).domain, generator U ⟨x, hx⟩ = z := by
  have hF : HasDerivAt (fun t : ℝ => ∫ s in (0:ℝ)..t, U s z) (U 0 z) 0 :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_apply hU z 0 0)
      ((continuous_apply hU z).stronglyMeasurableAtFilter _ _)
      (continuous_apply hU z).continuousAt
  have hF' : HasDerivAt (fun t : ℝ => ∫ s in (0:ℝ)..t, U s z) z 0 := by
    rw [hU.apply_zero] at hF
    simpa using hF
  have hderiv : HasDerivAt (fun t : ℝ => x + (I : ℂ) • ∫ s in (0:ℝ)..t, U s z)
      ((I : ℂ) • z) 0 := by
    simpa using (hF'.const_smul (I : ℂ)).const_add x
  have hfun : (fun t : ℝ => x + (I : ℂ) • ∫ s in (0:ℝ)..t, U s z)
      = fun t : ℝ => U t x := by
    funext t
    rw [← h t]
    abel
  rw [hfun] at hderiv
  exact ⟨mem_generator_domain hderiv, generator_apply_eq _ hderiv⟩

/-- The averages `e⁻¹ • ∫_0^e U s x ds` belong to the domain of the generator. -/
theorem average_mem_domain (x : H) (e : ℝ) :
    ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x) ∈ (generator U).domain := by
  set F : ℝ → H := fun u => ∫ s in (0:ℝ)..u, U s x with hFdef
  have hFderiv : ∀ u : ℝ, HasDerivAt F (U u x) u := by
    intro u
    exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_apply hU x 0 u)
      ((continuous_apply hU x).stronglyMeasurableAtFilter _ _)
      (continuous_apply hU x).continuousAt
  have hkey : ∀ t : ℝ, U t ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x)
      = (e⁻¹ : ℝ) • (F (e + t) - F t) := by
    intro t
    have h1 : U t ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x)
        = (e⁻¹ : ℝ) • U t (∫ s in (0:ℝ)..e, U s x) := by
      simp
    have h2 : U t (∫ s in (0:ℝ)..e, U s x) = ∫ s in (0:ℝ)..e, U t (U s x) :=
      (ContinuousLinearMap.intervalIntegral_comp_comm (U t) (intervalIntegrable_apply hU x 0 e)).symm
    have h3 : ∀ s : ℝ, U t (U s x) = U (s + t) x := by
      intro s
      have : U s * U t = U (s + t) := (hU.map_add s t).symm
      have hc : U t * U s = U (s + t) := by
        rw [← hU.map_add, add_comm]
      exact congrArg (fun L : H →L[ℂ] H => L x) hc
    have h4 : (∫ s in (0:ℝ)..e, U t (U s x)) = ∫ s in (0:ℝ)..e, U (s + t) x := by
      simp_rw [h3]
    have h5 : (∫ s in (0:ℝ)..e, U (s + t) x) = ∫ u in (0 + t)..(e + t), U u x :=
      intervalIntegral.integral_comp_add_right (fun u => U u x) t
    have h6 : (∫ u in (t:ℝ)..(e + t), U u x) = F (e + t) - F t := by
      rw [hFdef]
      exact (intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_apply hU x 0 (e + t)) (intervalIntegrable_apply hU x 0 t)).symm
    rw [h1, h2, h4, h5]
    simp only [zero_add]
    rw [h6]
  have hderiv : HasDerivAt (fun t : ℝ => (e⁻¹ : ℝ) • (F (e + t) - F t))
      ((e⁻¹ : ℝ) • (U e x - U 0 x)) 0 := by
    have hA : HasDerivAt (fun t : ℝ => F (e + t)) (U e x) 0 := by
      have hshift : HasDerivAt (fun t : ℝ => e + t) (1 : ℝ) 0 :=
        HasDerivAt.const_add e (hasDerivAt_id (0:ℝ))
      have h := HasDerivAt.scomp (0:ℝ) (hFderiv (e + 0)) hshift
      simpa [Function.comp] using h
    have hB : HasDerivAt (fun t : ℝ => F t) (U 0 x) 0 := hFderiv 0
    exact (hA.sub hB).const_smul (e⁻¹ : ℝ)
  have hfun : (fun t : ℝ => (e⁻¹ : ℝ) • (F (e + t) - F t))
      = fun t : ℝ => U t ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x) := by
    funext t; rw [hkey t]
  rw [hfun] at hderiv
  refine mem_generator_domain (y := (-I) • ((e⁻¹ : ℝ) • (U e x - U 0 x))) ?_
  have : (I : ℂ) • ((-I : ℂ) • ((e⁻¹ : ℝ) • (U e x - U 0 x)))
      = (e⁻¹ : ℝ) • (U e x - U 0 x) := by
    rw [smul_smul]
    simp [Complex.I_mul_I]
  rw [this]
  exact hderiv

/-- Quantitative approximation by the averages. -/
theorem norm_average_sub_le (x : H) {e d : ℝ} (he : 0 < e)
    (hd : ∀ s ∈ Set.uIoc (0:ℝ) e, ‖U s x - x‖ ≤ d) :
    ‖((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x) - x‖ ≤ d := by
  have hconst : (∫ _s in (0:ℝ)..e, x) = e • x := by
    simp
  have hx : x = (e⁻¹ : ℝ) • (∫ _s in (0:ℝ)..e, x) := by
    rw [hconst, smul_smul, inv_mul_cancel₀ (ne_of_gt he), one_smul]
  have hsub : ((e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, U s x) - x
      = (e⁻¹ : ℝ) • ∫ s in (0:ℝ)..e, (U s x - x) := by
    rw [intervalIntegral.integral_sub (intervalIntegrable_apply hU x 0 e)
      (intervalIntegrable_const)]
    rw [smul_sub, ← hx]
  rw [hsub, norm_smul]
  have hbound : ‖∫ s in (0:ℝ)..e, (U s x - x)‖ ≤ d * |e| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := e) (C := d)
      (f := fun s : ℝ => U s x - x) hd
    simpa using this
  have hnorm : ‖(e⁻¹ : ℝ)‖ = e⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  have habs : |e| = e := abs_of_pos he
  calc e⁻¹ * ‖∫ s in (0:ℝ)..e, (U s x - x)‖ ≤ e⁻¹ * (d * |e|) := by
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = d := by rw [habs]; field_simp

/-- The domain of the generator is dense. -/
theorem dense_domain : Dense ((generator U).domain : Set H) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro r hr
  have hcont : ContinuousAt (fun s : ℝ => U s x) 0 := (continuous_apply hU x).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨d, hd, hball⟩ := hcont (r/2) (by linarith)
  have hepos : 0 < d / 2 := by linarith
  have hbnd : ∀ s ∈ Set.uIoc (0:ℝ) (d/2), ‖U s x - x‖ ≤ r/2 := by
    intro s hs
    rw [Set.uIoc_of_le hepos.le] at hs
    have h1 : dist s 0 < d := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
      linarith [hs.2]
    have h2 := hball h1
    rw [hU.apply_zero] at h2
    simp only [ContinuousLinearMap.one_apply, dist_eq_norm] at h2
    exact h2.le
  refine ⟨((d/2)⁻¹ : ℝ) • ∫ s in (0:ℝ)..(d/2), U s x, average_mem_domain hU x (d/2), ?_⟩
  have hle := norm_average_sub_le hU x hepos hbnd
  have hdist : dist x (((d/2)⁻¹ : ℝ) • ∫ s in (0:ℝ)..(d/2), U s x)
      = ‖(((d/2)⁻¹ : ℝ) • ∫ s in (0:ℝ)..(d/2), U s x) - x‖ := by
    rw [dist_comm, dist_eq_norm]
  rw [hdist]
  linarith

/-- The generator is symmetric. -/
theorem generator_symmetric (x y : (generator U).domain) :
    ⟪generator U x, (y : H)⟫_ℂ = ⟪(x : H), generator U y⟫_ℂ := by
  have h1 := hasDerivAt_generator U x
  have h2 := hasDerivAt_generator U y
  have hprod := HasDerivAt.inner ℂ h1 h2
  have hconst : (fun t : ℝ => ⟪U t (x : H), U t (y : H)⟫_ℂ) = fun _ : ℝ => ⟪(x : H), (y : H)⟫_ℂ := by
    funext t; exact hU.inner_map_map t _ _
  rw [hconst] at hprod
  have hzero := hprod.unique (hasDerivAt_const (0:ℝ) ((⟪(x : H), (y : H)⟫_ℂ : ℂ)))
  rw [hU.apply_zero] at hzero
  simp only [ContinuousLinearMap.one_apply, inner_smul_right, inner_smul_left,
    Complex.conj_I] at hzero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hcancel : I * ⟪(x : H), generator U y⟫_ℂ = I * ⟪generator U x, (y : H)⟫_ℂ := by
    linear_combination hzero
  exact (mul_left_cancel₀ hI hcancel).symm

/-- A symmetric operator is contained in its adjoint. -/
theorem generator_le_adjoint : generator U ≤ (generator U).adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint (dense_domain hU) (fun x y => generator_symmetric hU x y)

/-- The basic norm identity for the symmetric generator. -/
theorem norm_sub_I_smul_sq (x : (generator U).domain) :
    ‖generator U x - I • (x : H)‖ ^ 2 = ‖generator U x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  have hreal : ⟪generator U x, (x : H)⟫_ℂ = (starRingEnd ℂ) (⟪generator U x, (x : H)⟫_ℂ) := by
    rw [inner_conj_symm]
    exact generator_symmetric hU x x
  have him : (⟪generator U x, (x : H)⟫_ℂ).im = 0 := by
    have := congrArg Complex.im hreal
    simp only [Complex.conj_im] at this
    linarith
  have hnorm : ‖(I : ℂ) • (x : H)‖ = ‖(x : H)‖ := by
    rw [norm_smul]; simp
  have hre : RCLike.re (⟪generator U x, (I : ℂ) • (x : H)⟫_ℂ) = 0 := by
    rw [inner_smul_right]
    simp [RCLike.re_to_complex, him]
  rw [@norm_sub_sq ℂ, hnorm, hre]
  ring

theorem norm_integral_sub_le (a b : H) (t : ℝ) :
    ‖(∫ s in (0:ℝ)..t, U s a) - ∫ s in (0:ℝ)..t, U s b‖ ≤ ‖a - b‖ * |t| := by
  rw [← intervalIntegral.integral_sub (intervalIntegrable_apply hU a 0 t)
    (intervalIntegrable_apply hU b 0 t)]
  have hfun : ∀ s : ℝ, U s a - U s b = U s (a - b) := by
    intro s; simp [map_sub]
  simp_rw [hfun]
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := t)
    (C := ‖a - b‖) (f := fun s : ℝ => U s (a - b)) (fun s _ => le_of_eq (hU.norm_map s (a - b)))
  simpa using hle

theorem tendsto_integral_of_tendsto {v : ℕ → H} {w : H} (t : ℝ)
    (hv : Filter.Tendsto v Filter.atTop (nhds w)) :
    Filter.Tendsto (fun n => ∫ s in (0:ℝ)..t, U s (v n)) Filter.atTop
      (nhds (∫ s in (0:ℝ)..t, U s w)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _)
    (fun n => norm_integral_sub_le hU (v n) w t) ?_
  have h0 : Filter.Tendsto (fun n => ‖v n - w‖) Filter.atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  simpa using h0.mul_const |t|

/-- The generator is a closed operator. -/
theorem generator_isClosed : (generator U).IsClosed := by
  have hseq : IsSeqClosed ((generator U).graph : Set (H × H)) := by
    intro p q hp hpq
    have h1 : Filter.Tendsto (fun n => (p n).1) Filter.atTop (nhds q.1) :=
      (continuous_fst.tendsto q).comp hpq
    have h2 : Filter.Tendsto (fun n => (p n).2) Filter.atTop (nhds q.2) :=
      (continuous_snd.tendsto q).comp hpq
    have key : ∀ t : ℝ, U t q.1 - q.1 = (I : ℂ) • ∫ s in (0:ℝ)..t, U s q.2 := by
      intro t
      have hEq : ∀ n, (I : ℂ) • (∫ s in (0:ℝ)..t, U s ((p n).2)) = U t ((p n).1) - (p n).1 := by
        intro n
        obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).mp (hp n)
        have hform := integral_formula hU y t
        rw [hy1, hy2] at hform
        exact hform
      have hL : Filter.Tendsto (fun n => (I : ℂ) • ∫ s in (0:ℝ)..t, U s ((p n).2)) Filter.atTop
          (nhds ((I : ℂ) • ∫ s in (0:ℝ)..t, U s q.2)) :=
        (tendsto_integral_of_tendsto hU t h2).const_smul (I : ℂ)
      have hR : Filter.Tendsto (fun n => U t ((p n).1) - (p n).1) Filter.atTop
          (nhds (U t q.1 - q.1)) :=
        (((U t).continuous.tendsto q.1).comp h1).sub h1
      have hL' : Filter.Tendsto (fun n => U t ((p n).1) - (p n).1) Filter.atTop
          (nhds ((I : ℂ) • ∫ s in (0:ℝ)..t, U s q.2)) := by
        simpa [hEq] using hL
      exact tendsto_nhds_unique hR hL'
    obtain ⟨hx, hAx⟩ := mem_domain_of_integral_eq hU q.1 q.2 key
    exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨q.1, hx⟩, rfl, hAx⟩
  exact hseq.isClosed

/-- The deficiency spaces are trivial. -/
theorem eq_zero_of_adjoint_eq_smul (c : ℂ) (hc : c = I ∨ c = -I)
    (f : ((generator U).adjoint).domain) (h : (generator U).adjoint f = c • (f : H)) :
    (f : H) = 0 := by
  obtain ⟨r, hr2, hrc⟩ : ∃ r : ℝ, r * r = 1 ∧ (starRingEnd ℂ) I * c = (r : ℂ) := by
    rcases hc with rfl | rfl
    · exact ⟨1, by norm_num, by simp [Complex.I_mul_I]⟩
    · exact ⟨-1, by norm_num, by simp [Complex.I_mul_I]⟩
  have hdense := dense_domain hU
  have hformal := LinearPMap.adjoint_isFormalAdjoint (T := generator U) hdense
  refine hdense.eq_zero_of_inner_right ?_
  intro ψ
  set g : ℝ → ℂ := fun t => ⟪U t (ψ : H), (f : H)⟫_ℂ with hgdef
  have hgderiv : ∀ t : ℝ, HasDerivAt g ((r : ℂ) * g t) t := by
    intro t
    have h1 := hasDerivAt_of_mem_domain hU ψ t
    have h2 : HasDerivAt (fun _ : ℝ => (f : H)) 0 t := hasDerivAt_const t _
    have h3 := HasDerivAt.inner ℂ h1 h2
    have h5 : U t (generator U ψ) = generator U ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩ :=
      (generator_comm hU ψ t).symm
    have hfa := hformal f ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩
    have h6 : ⟪generator U ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩, (f : H)⟫_ℂ
        = c * g t := by
      have hconj : ⟪generator U ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩, (f : H)⟫_ℂ
          = (starRingEnd ℂ) ⟪(f : H), generator U ⟨U t (ψ : H), apply_mem_domain hU ψ t⟩⟫_ℂ := by
        rw [inner_conj_symm]
      rw [hconj, ← hfa, h, inner_smul_left]
      simp only [hgdef]
      rw [← inner_conj_symm ((f : H)) (U t (ψ : H))]
      simp [mul_comm]
    have h7 : ⟪(I : ℂ) • U t (generator U ψ), (f : H)⟫_ℂ = (r : ℂ) * g t := by
      rw [inner_smul_left, h5, h6, ← mul_assoc, hrc]
    simpa [h7] using h3
  have hbound : ∀ t : ℝ, ‖g t‖ ≤ ‖(ψ : H)‖ * ‖(f : H)‖ := by
    intro t
    have h1 : ‖g t‖ ≤ ‖U t (ψ : H)‖ * ‖(f : H)‖ := norm_inner_le_norm _ _
    rwa [hU.norm_map t (ψ : H)] at h1
  have hg0 : g 0 = 0 := by
    by_contra hne
    set a : ℝ := ‖g 0‖ with hadef
    have hapos : 0 < a := by
      rw [hadef, norm_pos_iff]
      exact hne
    set C : ℝ := ‖(ψ : H)‖ * ‖(f : H)‖ with hCdef
    have hCnonneg : 0 ≤ C := by positivity
    set T : ℝ := (C + 1) / a with hTdef
    have hTpos : 0 < T := by positivity
    have hval := eq_exp_mul_of_hasDerivAt r hgderiv (r * T)
    have hexp : ((r : ℂ) * ((r * T : ℝ) : ℂ)) = ((T : ℝ) : ℂ) := by
      push_cast
      rw [← mul_assoc]
      norm_cast
      rw [hr2, one_mul]
    rw [hexp] at hval
    have hnorm : ‖g (r * T)‖ = Real.exp T * a := by
      rw [hval, norm_mul, hadef]
      congr 1
      rw [← Complex.ofReal_exp]
      simp
    have hle := hbound (r * T)
    rw [hnorm] at hle
    have hexpge : 1 + T ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
    have hTa : T * a = C + 1 := by
      rw [hTdef]
      field_simp
    have h9 : (1 + T) * a ≤ Real.exp T * a := mul_le_mul_of_nonneg_right hexpge hapos.le
    nlinarith [h9, hTa, hapos, hle]
  have h0 : U 0 (ψ : H) = (ψ : H) := by rw [hU.apply_zero]; rfl
  rw [hgdef] at hg0
  simpa [h0] using hg0

/-- `A - i` is surjective. -/
theorem exists_sub_I_eq (z : H) :
    ∃ x : (generator U).domain, generator U x - I • (x : H) = z := by
  have hGclosed : IsClosed (((generator U).graph : Submodule ℂ (H × H)) : Set (H × H)) :=
    generator_isClosed hU
  haveI : CompleteSpace ↑((generator U).graph) := hGclosed.completeSpace_coe
  set S : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) - I • (ContinuousLinearMap.fst ℂ H H) with hS
  set phi : ↑((generator U).graph) →L[ℂ] H := S.comp ((generator U).graph).subtypeL with hphi
  have hphi_apply : ∀ p : ↑((generator U).graph),
      phi p = (p : H × H).2 - I • (p : H × H).1 := by
    intro p
    simp [hphi, hS]
  have hgraph_mem : ∀ x : (generator U).domain,
      (((x : H), generator U x) : H × H) ∈ (generator U).graph := by
    intro x
    exact (LinearPMap.mem_graph_iff _).mpr ⟨x, rfl, rfl⟩
  set K : Submodule ℂ H := LinearMap.range (phi : ↑((generator U).graph) →ₗ[ℂ] H) with hK
  have hmemK : ∀ x : (generator U).domain,
      (generator U x - I • (x : H)) ∈ K := by
    intro x
    refine ⟨⟨((x : H), generator U x), hgraph_mem x⟩, ?_⟩
    simpa using hphi_apply ⟨((x : H), generator U x), hgraph_mem x⟩
  -- the range is closed
  have hanti : AntilipschitzWith 1 phi := by
    refine AddMonoidHomClass.antilipschitz_of_bound phi ?_
    intro p
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).mp p.2
    have hp1 : (p : H × H).1 = (x : H) := hx1.symm
    have hp2 : (p : H × H).2 = generator U x := hx2.symm
    have hnormsq : ‖phi p‖ ^ 2 = ‖generator U x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
      rw [hphi_apply p, hp1, hp2]
      exact norm_sub_I_smul_sq hU x
    have hpn : ‖(p : H × H)‖ = max ‖(x : H)‖ ‖generator U x‖ := by
      rw [Prod.norm_def, hp1, hp2]
    have h1 : ‖(p : H × H)‖ ^ 2 ≤ ‖phi p‖ ^ 2 := by
      rw [hpn, hnormsq]
      rcases max_cases ‖(x : H)‖ ‖generator U x‖ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
        nlinarith [norm_nonneg (x : H), norm_nonneg (generator U x)]
    have h2 : ‖(p : H × H)‖ ≤ ‖phi p‖ := by
      nlinarith [norm_nonneg (p : H × H), norm_nonneg (phi p), h1]
    simpa using h2
  have hclosedrange : IsClosed (Set.range phi) :=
    hanti.isClosed_range phi.uniformContinuous
  have hKclosed : IsClosed (K : Set H) := by
    rw [hK, LinearMap.coe_range]
    exact hclosedrange
  haveI : CompleteSpace ↑K := hKclosed.completeSpace_coe
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  -- the orthogonal complement is trivial
  have hbot : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have horth : ∀ x : (generator U).domain, ⟪generator U x - I • (x : H), y⟫_ℂ = 0 := by
      intro x
      exact (Submodule.mem_orthogonal K y).mp hy _ (hmemK x)
    have hkey : ∀ x : (generator U).domain, ⟪(-I : ℂ) • y, (x : H)⟫_ℂ = ⟪y, generator U x⟫_ℂ := by
      intro x
      have h0 := horth x
      rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
      have h1 : ⟪generator U x, y⟫_ℂ = -I * ⟪(x : H), y⟫_ℂ := by
        simpa [Complex.conj_I] using h0
      have h2 : ⟪y, generator U x⟫_ℂ = (starRingEnd ℂ) (⟪generator U x, y⟫_ℂ) := by
        rw [inner_conj_symm]
      rw [h2, h1, inner_smul_left, map_mul, inner_conj_symm]
    have hydom : y ∈ ((generator U).adjoint).domain :=
      LinearPMap.mem_adjoint_domain_of_exists y ⟨(-I : ℂ) • y, hkey⟩
    have hyval : (generator U).adjoint ⟨y, hydom⟩ = (-I : ℂ) • y :=
      LinearPMap.adjoint_apply_eq (dense_domain hU) ⟨y, hydom⟩ hkey
    exact eq_zero_of_adjoint_eq_smul hU (-I) (Or.inr rfl) ⟨y, hydom⟩ hyval
  have hKtop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
  have hz : z ∈ K := by rw [hKtop]; trivial
  obtain ⟨p, hp⟩ := hz
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).mp p.2
  refine ⟨x, ?_⟩
  have := hphi_apply p
  rw [← hx1, ← hx2] at this
  rw [← hp]
  simpa using this.symm

/-- Every element of the domain of the adjoint lies in the domain of the generator. -/
theorem mem_domain_of_mem_adjoint_domain (f : H) (hf : f ∈ ((generator U).adjoint).domain) :
    ∃ h : f ∈ (generator U).domain,
      generator U ⟨f, h⟩ = (generator U).adjoint ⟨f, hf⟩ := by
  have hle := generator_le_adjoint hU
  obtain ⟨ψ, hψ⟩ := exists_sub_I_eq hU ((generator U).adjoint ⟨f, hf⟩ - I • f)
  have hψd : ((ψ : H)) ∈ ((generator U).adjoint).domain := hle.1 ψ.2
  have hAdψ : (generator U).adjoint ⟨(ψ : H), hψd⟩ = generator U ψ := (hle.2 rfl).symm
  have hsub : f - (ψ : H) ∈ ((generator U).adjoint).domain :=
    Submodule.sub_mem _ hf hψd
  have hval : (generator U).adjoint ⟨f - (ψ : H), hsub⟩ = I • (f - (ψ : H)) := by
    have hlin : (generator U).adjoint ⟨f - (ψ : H), hsub⟩
        = (generator U).adjoint ⟨f, hf⟩ - (generator U).adjoint ⟨(ψ : H), hψd⟩ := by
      have := ((generator U).adjoint).map_sub ⟨f, hf⟩ ⟨(ψ : H), hψd⟩
      simpa using this
    rw [hlin, hAdψ]
    have : generator U ψ = ((generator U).adjoint ⟨f, hf⟩ - I • f) + I • (ψ : H) := by
      rw [← hψ]; abel
    rw [this, smul_sub]
    abel
  have hzero : ((⟨f - (ψ : H), hsub⟩ : ((generator U).adjoint).domain) : H) = 0 :=
    eq_zero_of_adjoint_eq_smul hU I (Or.inl rfl) ⟨f - (ψ : H), hsub⟩ hval
  have hfψ : f = (ψ : H) := by
    have h0 : f - (ψ : H) = 0 := hzero
    exact sub_eq_zero.mp h0
  subst hfψ
  refine ⟨ψ.2, ?_⟩
  rw [hAdψ]

/-- **Stone's theorem**: the generator of a strongly continuous one-parameter unitary group is
self-adjoint, i.e. `A† = A`. -/
theorem stone_generator :
    IsSelfAdjoint (generator U) ∧
      (∀ x : (generator U).domain,
        HasDerivAt (fun t => U t (x : H)) (I • generator U x) 0) ∧
      (∀ x y : H, HasDerivAt (fun t => U t x) (I • y) 0 →
        ∃ h : x ∈ (generator U).domain, generator U ⟨x, h⟩ = y) := by
  refine ⟨?_, hasDerivAt_generator U, ?_⟩
  · have hle1 : (generator U).adjoint ≤ generator U := by
      refine ⟨?_, ?_⟩
      · intro f hf
        exact (mem_domain_of_mem_adjoint_domain hU f hf).choose
      · rintro ⟨f, hf⟩ ⟨g, hg⟩ (hfg : f = g)
        subst hfg
        exact ((mem_domain_of_mem_adjoint_domain hU f hf).choose_spec).symm
    exact le_antisymm hle1 (generator_le_adjoint hU)
  · intro x y hxy
    exact ⟨mem_generator_domain hxy, generator_apply_eq _ hxy⟩

end Analysis

/-- Sanity check: the trivial group `U t = 1` is a strongly continuous one-parameter unitary
group, so the hypothesis of Stone's theorem is satisfiable. -/
example : IsUnitaryGroup (fun _ : ℝ => (1 : H →L[ℂ] H)) where
  mem_unitary := fun _ => one_mem _
  map_add := fun _ _ => by simp
  strong_continuous := fun _ => continuous_const

end QPhys

