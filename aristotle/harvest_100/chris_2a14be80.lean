import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`. -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = ContinuousLinearMap.id ℂ H
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  inner_map : ∀ t x y, ⟪U t x, U t y⟫_ℂ = ⟪x, y⟫_ℂ
  cont : ∀ x, Continuous fun t => U t x

variable {U : ℝ → H →L[ℂ] H}

/-- The natural domain of the generator: those vectors for which `t ↦ U t x` is
differentiable at `0`. -/
def domain (U : ℝ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x | ∃ y, HasDerivAt (fun t : ℝ => U t x) y 0}
  add_mem' := by
    rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
    exact ⟨ya + yb, by simpa using ha.add hb⟩
  zero_mem' := ⟨0, by simpa using (hasDerivAt_const (0:ℝ) (0:H))⟩
  smul_mem' := by
    rintro c a ⟨ya, ha⟩
    exact ⟨c • ya, by simpa using ha.const_smul c⟩

/-- The generator `A` of the unitary group, defined so that `U t = exp (i t A)`, i.e.
`A x = -i * (d/dt) U t x |_{t=0}`. -/
noncomputable def generator (U : ℝ → H →L[ℂ] H) (x : H) : H :=
  -Complex.I • deriv (fun t : ℝ => U t x) 0

omit [CompleteSpace H] in
theorem generator_eq {x y : H} (h : HasDerivAt (fun t : ℝ => U t x) y 0) :
    generator U x = -Complex.I • y := by
  rw [generator, h.deriv]

omit [CompleteSpace H] in
theorem hasDerivAt_of_mem_domain {x : H} (hx : x ∈ domain U) :
    HasDerivAt (fun t : ℝ => U t x) (Complex.I • generator U x) 0 := by
  obtain ⟨y, hy⟩ := hx
  rw [generator_eq hy, smul_smul]
  simpa using hy

omit [CompleteSpace H] in
theorem clm_comp_hasDerivAt (L : H →L[ℂ] H) {f : ℝ → H} {f' : H} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun s => L (f s)) (L f') t := by
  simpa using (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

/-- On the domain, `t ↦ U t x` is differentiable everywhere. -/
theorem hasDerivAt_all (hU : IsUnitaryGroup U) {x : H} (hx : x ∈ domain U) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U s x) (U t (Complex.I • generator U x)) t := by
  have h0 := hasDerivAt_of_mem_domain hx
  have h1 : HasDerivAt (fun s : ℝ => U (s - t) x) (Complex.I • generator U x) t :=
    HasDerivAt.comp_sub_const (f := fun u : ℝ => U u x) t t (by simpa using h0)
  have h2 := clm_comp_hasDerivAt (U t) h1
  have key : ∀ s : ℝ, U t (U (s - t) x) = U s x := by
    intro s
    have e : t + (s - t) = s := by ring
    rw [← ContinuousLinearMap.comp_apply, ← hU.map_add, e]
  simpa only [key] using h2

/-- The domain is invariant, and the generator commutes with the group. -/
theorem translate_mem_domain (hU : IsUnitaryGroup U) {x : H} (hx : x ∈ domain U) (t : ℝ) :
    U t x ∈ domain U ∧ generator U (U t x) = U t (generator U x) := by
  have h1 : HasDerivAt (fun s : ℝ => U (s + t) x) (U t (Complex.I • generator U x)) 0 :=
    HasDerivAt.comp_add_const (f := fun u : ℝ => U u x) 0 t (by simpa using hasDerivAt_all hU hx t)
  have key : ∀ s : ℝ, U (s + t) x = U s (U t x) := by
    intro s
    rw [← ContinuousLinearMap.comp_apply, ← hU.map_add]
  rw [funext key] at h1
  refine ⟨⟨_, h1⟩, ?_⟩
  rw [generator_eq h1, map_smul, smul_smul]
  simp

omit [CompleteSpace H] in
theorem generator_add {x y : H} (hx : x ∈ domain U)
    (hy : y ∈ domain U) : generator U (x + y) = generator U x + generator U y := by
  have hxy : HasDerivAt (fun t : ℝ => U t (x + y))
      (Complex.I • generator U x + Complex.I • generator U y) 0 := by
    simpa using (hasDerivAt_of_mem_domain hx).add (hasDerivAt_of_mem_domain hy)
  rw [generator_eq hxy, smul_add, smul_smul, smul_smul]
  simp

omit [CompleteSpace H] in
theorem generator_smul (c : ℂ) {x : H} (hx : x ∈ domain U) :
    generator U (c • x) = c • generator U x := by
  have hcx : HasDerivAt (fun t : ℝ => U t (c • x)) (c • (Complex.I • generator U x)) 0 := by
    simpa using (hasDerivAt_of_mem_domain hx).const_smul c
  have hI : -Complex.I * c * Complex.I = c := by
    rw [show -Complex.I * c * Complex.I = -(Complex.I * Complex.I) * c by ring, Complex.I_mul_I]
    ring
  rw [generator_eq hcx, smul_smul, smul_smul, hI]

theorem generator_symmetric (hU : IsUnitaryGroup U) {x y : H} (hx : x ∈ domain U)
    (hy : y ∈ domain U) : ⟪generator U x, y⟫_ℂ = ⟪x, generator U y⟫_ℂ := by
  have hf := hasDerivAt_of_mem_domain hx
  have hg := hasDerivAt_of_mem_domain hy
  have hc : HasDerivAt (fun t : ℝ => ⟪U t x, U t y⟫_ℂ) 0 0 := by
    have he : (fun t : ℝ => ⟪U t x, U t y⟫_ℂ) = fun _ => ⟪x, y⟫_ℂ :=
      funext fun t => hU.inner_map t x y
    rw [he]; exact hasDerivAt_const _ _
  have hd := hf.inner ℂ hg
  have hu := hc.unique hd
  rw [hU.map_zero] at hu
  simp only [ContinuousLinearMap.id_apply, inner_smul_right, inner_smul_left,
    Complex.conj_I] at hu
  have hmul : Complex.I * ⟪x, generator U y⟫_ℂ = Complex.I * ⟪generator U x, y⟫_ℂ := by
    linear_combination -hu
  exact (mul_left_cancel₀ Complex.I_ne_zero hmul).symm

/-- Fundamental theorem of calculus for the orbit map. -/
theorem hasDerivAt_integral (hU : IsUnitaryGroup U) (x : H) (t : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ s in (0:ℝ)..r, U s x) (U t x) t := by
  have hf : Continuous fun s : ℝ => U s x := hU.cont x
  exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem integral_mem_domain (hU : IsUnitaryGroup U) (x : H) (r : ℝ) :
    (∫ s in (0:ℝ)..r, U s x) ∈ domain U := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => U s x) MeasureTheory.volume a b :=
    fun a b => (hU.cont x).intervalIntegrable a b
  have key : ∀ t : ℝ, U t (∫ s in (0:ℝ)..r, U s x)
      = (∫ s in (0:ℝ)..(t + r), U s x) - (∫ s in (0:ℝ)..t, U s x) := by
    intro t
    have h1 : U t (∫ s in (0:ℝ)..r, U s x) = ∫ s in (0:ℝ)..r, U t (U s x) :=
      (ContinuousLinearMap.intervalIntegral_comp_comm (U t) (hint 0 r)).symm
    have h2 : ∀ s : ℝ, U t (U s x) = U (t + s) x := by
      intro s; rw [← ContinuousLinearMap.comp_apply, ← hU.map_add]
    rw [h1]
    simp_rw [h2]
    rw [intervalIntegral.integral_comp_add_left (fun u : ℝ => U u x) t, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hint 0 (t + r)) (hint 0 t)).symm
  refine ⟨U r x - x, ?_⟩
  have hd : HasDerivAt
      (fun t : ℝ => (∫ s in (0:ℝ)..(t + r), U s x) - (∫ s in (0:ℝ)..t, U s x))
      (U (0 + r) x - U 0 x) 0 :=
    (HasDerivAt.comp_add_const (f := fun u : ℝ => ∫ s in (0:ℝ)..u, U s x) 0 r
      (hasDerivAt_integral hU x (0 + r))).sub (hasDerivAt_integral hU x 0)
  simp only [zero_add, hU.map_zero, ContinuousLinearMap.id_apply] at hd
  simpa only [key] using hd

theorem dense_domain (hU : IsUnitaryGroup U) : Dense (domain U : Set H) := by
  intro x
  have hG : HasDerivAt (fun r : ℝ => ∫ s in (0:ℝ)..r, U s x) x 0 := by
    simpa [hU.map_zero] using hasDerivAt_integral hU x 0
  have hslope := hasDerivAt_iff_tendsto_slope.mp hG
  refine mem_closure_of_tendsto hslope ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have h0 : (∫ s in (0:ℝ)..(0:ℝ), U s x) = 0 := intervalIntegral.integral_same
  rw [slope_def_module, h0, sub_zero, sub_zero, ← Complex.coe_smul]
  exact Submodule.smul_mem _ _ (integral_mem_domain hU x t)

omit [CompleteSpace H] in
theorem inner_left_shift (hU : IsUnitaryGroup U) (t : ℝ) (a b : H) :
    ⟪U t a, b⟫_ℂ = ⟪a, U (-t) b⟫_ℂ := by
  have hb : U t (U (-t) b) = b := by
    rw [← ContinuousLinearMap.comp_apply, ← hU.map_add, add_neg_cancel, hU.map_zero]
    rfl
  calc ⟪U t a, b⟫_ℂ = ⟪U t a, U t (U (-t) b)⟫_ℂ := by rw [hb]
    _ = ⟪a, U (-t) b⟫_ℂ := hU.inner_map t a _

/-- A vector orthogonal to the (dense) domain vanishes. -/
theorem eq_zero_of_inner_domain (hU : IsUnitaryGroup U) {w : H}
    (hw : ∀ x ∈ domain U, ⟪x, w⟫_ℂ = 0) : w = 0 := by
  have hcont : Continuous fun v : H => ⟪v, w⟫_ℂ := continuous_id.inner continuous_const
  have hall : (fun v : H => ⟪v, w⟫_ℂ) = fun _ : H => (0 : ℂ) :=
    Continuous.ext_on (dense_domain hU) hcont continuous_const hw
  have : ⟪w, w⟫_ℂ = 0 := congrFun hall w
  exact inner_self_eq_zero.mp this

theorem generator_maximal (hU : IsUnitaryGroup U) {y z : H}
    (h : ∀ x ∈ domain U, ⟪generator U x, y⟫_ℂ = ⟪x, z⟫_ℂ) :
    y ∈ domain U ∧ generator U y = z := by
  have hzc : Continuous fun s : ℝ => U (-s) z := (hU.cont z).comp continuous_neg
  set W : ℝ → H := fun t => ∫ s in (0:ℝ)..t, U (-s) z with hWdef
  have key : ∀ t : ℝ, U (-t) y - y = -Complex.I • W t := by
    intro t
    have hall : ∀ x ∈ domain U, ⟪x, (U (-t) y - y) + Complex.I • W t⟫_ℂ = 0 := by
      intro x hx
      have hderiv : ∀ s : ℝ, HasDerivAt (fun u : ℝ => ⟪U u x, y⟫_ℂ)
          (-Complex.I * ⟪U s x, z⟫_ℂ) s := by
        intro s
        have h1 := (hasDerivAt_all hU hx s).inner ℂ (hasDerivAt_const s y)
        have h2 : ⟪U s (Complex.I • generator U x), y⟫_ℂ = -Complex.I * ⟪U s x, z⟫_ℂ := by
          rw [map_smul, inner_smul_left, Complex.conj_I,
            ← (translate_mem_domain hU hx s).2, h _ (translate_mem_domain hU hx s).1]
        simpa [h2] using h1
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u : ℝ => ⟪U u x, y⟫_ℂ) (f' := fun s : ℝ => -Complex.I * ⟪U s x, z⟫_ℂ)
        (a := 0) (b := t) (fun s _ => hderiv s)
        ((continuous_const.mul ((hU.cont x).inner continuous_const)).intervalIntegrable 0 t)
      have hsplit : (∫ s in (0:ℝ)..t, -Complex.I * ⟪U s x, z⟫_ℂ)
          = -Complex.I * ⟪x, W t⟫_ℂ := by
        have h3 : ∀ s : ℝ, -Complex.I * ⟪U s x, z⟫_ℂ
            = -Complex.I * (innerSL ℂ x) (U (-s) z) := by
          intro s; rw [inner_left_shift hU s x z]; rfl
        simp_rw [h3]
        rw [intervalIntegral.integral_const_mul,
          ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ x)
            (hzc.intervalIntegrable 0 t)]
        rfl
      rw [hsplit, inner_left_shift hU t x y, hU.map_zero] at hFTC
      simp only [ContinuousLinearMap.id_apply] at hFTC
      rw [inner_add_right, inner_sub_right, inner_smul_right]
      linear_combination hFTC
    have hzero := eq_zero_of_inner_domain hU hall
    have := sub_eq_zero.mp ?_
    · exact this
    · rw [sub_eq_iff_eq_add] at *
      linear_combination (norm := module) hzero
  have hW : HasDerivAt W z 0 := by
    have := intervalIntegral.integral_hasDerivAt_right (f := fun s : ℝ => U (-s) z)
      (a := 0) (b := 0) (hzc.intervalIntegrable 0 0)
      hzc.stronglyMeasurable.stronglyMeasurableAtFilter hzc.continuousAt
    simpa [hWdef, hU.map_zero] using this
  have hneg : HasDerivAt (fun t : ℝ => U (-t) y) (-Complex.I • z) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => y + (-Complex.I) • W t) ((-Complex.I) • z) 0 :=
      (hW.const_smul (-Complex.I)).const_add y
    have h2 : (fun t : ℝ => y + (-Complex.I) • W t) = fun t : ℝ => U (-t) y := by
      funext t
      rw [← key t]
      abel
    rwa [h2] at h1
  have hcomp := HasDerivAt.scomp (𝕜 := ℝ) (g₁ := fun t : ℝ => U (-t) y)
    (h := fun t : ℝ => -t) 0 (by simpa using hneg) (hasDerivAt_neg 0)
  have hfun : ((fun t : ℝ => U (-t) y) ∘ fun t : ℝ => -t) = fun t : ℝ => U t y := by
    funext t; simp
  rw [hfun] at hcomp
  have hval : ((-1 : ℝ) • (-Complex.I • z)) = Complex.I • z := by
    rw [← Complex.coe_smul, smul_smul]
    norm_num
  rw [hval] at hcomp
  exact ⟨⟨_, hcomp⟩, by rw [generator_eq hcomp, smul_smul]; simp⟩

/-- **Stone's theorem**: the generator of a strongly continuous one-parameter unitary group
is a densely defined, linear, self-adjoint operator.  Here self-adjointness means both that
the generator is symmetric on its domain and that it is maximal in the sense that any vector
`y` in the domain of the adjoint already lies in the domain of the generator, with matching
value. -/
theorem stone_generator (hU : IsUnitaryGroup U) :
    Dense (domain U : Set H) ∧
    (∀ x ∈ domain U, ∀ y ∈ domain U,
      generator U (x + y) = generator U x + generator U y) ∧
    (∀ (c : ℂ), ∀ x ∈ domain U, generator U (c • x) = c • generator U x) ∧
    (∀ x ∈ domain U, ∀ y ∈ domain U, ⟪generator U x, y⟫_ℂ = ⟪x, generator U y⟫_ℂ) ∧
    (∀ y z : H, (∀ x ∈ domain U, ⟪generator U x, y⟫_ℂ = ⟪x, z⟫_ℂ) →
      y ∈ domain U ∧ generator U y = z) := by
  refine ⟨dense_domain hU, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy; exact generator_add hx hy
  · intro c x hx; exact generator_smul c hx
  · intro x hx y hy; exact generator_symmetric hU hx hy
  · intro y z h; exact generator_maximal hU h

end QPhys

