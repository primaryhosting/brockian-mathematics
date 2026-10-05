/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Mathlib (as of this version) contains no form of Stone's theorem on one-parameter unitary
groups, so the generator, its domain, and the proof of self-adjointness are developed here
from scratch.  The Mathlib inputs used are the fundamental theorem of calculus for
Banach-space valued interval integrals (`intervalIntegral.integral_hasDerivAt_right`,
`intervalIntegral.integral_eq_sub_of_hasDerivAt`), the fact that continuous linear maps
commute with interval integrals (`ContinuousLinearMap.intervalIntegral_comp_comm`),
differentiability of the inner product (`HasDerivAt.inner`), and
`Dense.eq_of_inner_right`.
-/

namespace QPhys

open Complex MeasureTheory intervalIntegral
open scoped Classical

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The domain of the generator of a one-parameter group `U : ℝ → H →L[ℂ] H`:
the set of vectors `x` for which `t ↦ U t x` is differentiable at `0`.  We write the
derivative as `Complex.I • z`, so that `U t = exp (t • (I • A))`, i.e. `A` is the
"physicist's" generator (`U t = exp (i t A)`). -/
def genDom (U : ℝ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x | ∃ z, HasDerivAt (fun t => U t x) (Complex.I • z) 0}
  add_mem' := by
    rintro x y ⟨z, hz⟩ ⟨w, hw⟩
    refine ⟨z + w, ?_⟩
    have : (fun t => U t (x + y)) = fun t => U t x + U t y := by
      funext t; simp
    rw [this, smul_add]
    exact hz.add hw
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp only [map_zero, smul_zero]
    exact hasDerivAt_const _ _
  smul_mem' := by
    rintro c x ⟨z, hz⟩
    refine ⟨c • z, ?_⟩
    have : (fun t => U t (c • x)) = fun t => c • U t x := by
      funext t; simp
    rw [this, smul_comm]
    exact hz.const_smul c

/-- The generator `A` of a one-parameter group: `A x` is the unique `z` with
`(d/dt) U t x |_{t=0} = I • z`, and `0` off the domain. -/
noncomputable def gen (U : ℝ → H →L[ℂ] H) (x : H) : H :=
  if h : ∃ z, HasDerivAt (fun t => U t x) (Complex.I • z) 0 then h.choose else 0

variable {U : ℝ → H →L[ℂ] H}

omit [CompleteSpace H] in
theorem mem_genDom_iff {x : H} :
    x ∈ genDom U ↔ ∃ z, HasDerivAt (fun t => U t x) (Complex.I • z) 0 := Iff.rfl

omit [CompleteSpace H] in
theorem hasDerivAt_gen {x : H} (hx : x ∈ genDom U) :
    HasDerivAt (fun t => U t x) (Complex.I • gen U x) 0 := by
  have h : ∃ z, HasDerivAt (fun t => U t x) (Complex.I • z) 0 := hx
  rw [gen, dif_pos h]
  exact h.choose_spec

omit [CompleteSpace H] in
theorem gen_eq {x z : H} (h : HasDerivAt (fun t => U t x) (Complex.I • z) 0) :
    gen U x = z := by
  have hx : x ∈ genDom U := ⟨z, h⟩
  have h2 := (hasDerivAt_gen hx).unique h
  have : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  exact smul_right_injective H this h2

omit [CompleteSpace H] in
/-- Membership together with the value of the generator. -/
theorem mem_genDom_and_gen_eq {x z : H} (h : HasDerivAt (fun t => U t x) (Complex.I • z) 0) :
    x ∈ genDom U ∧ gen U x = z := ⟨⟨z, h⟩, gen_eq h⟩

section GroupFacts

variable (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = (U s).comp (U t))
  (hnorm : ∀ t x, ‖U t x‖ = ‖x‖)

omit [CompleteSpace H] in
include hadd in
theorem U_apply_U (s t : ℝ) (x : H) : U s (U t x) = U (s + t) x := by
  rw [hadd s t]; rfl

omit [CompleteSpace H] in
include h0 hadd in
theorem U_neg_apply (t : ℝ) (x : H) : U t (U (-t) x) = x := by
  rw [U_apply_U hadd, add_neg_cancel, h0]; rfl

omit [CompleteSpace H] in
include hnorm in
theorem inner_U_U (t : ℝ) (x y : H) : inner ℂ (U t x) (U t y) = inner ℂ x y := by
  let L : H →ₗᵢ[ℂ] H := ⟨(U t).toLinearMap, hnorm t⟩
  exact L.inner_map_map x y

omit [CompleteSpace H] in
include h0 hadd hnorm in
theorem inner_U_left (t : ℝ) (x y : H) : inner ℂ (U t x) y = inner ℂ x (U (-t) y) := by
  conv_lhs => rw [show y = U t (U (-t) y) from (U_neg_apply h0 hadd t y).symm]
  exact inner_U_U hnorm t x (U (-t) y)

end GroupFacts

section Generator

variable (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = (U s).comp (U t))
  (hnorm : ∀ t x, ‖U t x‖ = ‖x‖) (hcont : ∀ x : H, Continuous fun t => U t x)

omit [CompleteSpace H] in
include hadd in
/-- The domain of the generator is invariant under the group, and the generator commutes
with the group. -/
theorem U_mem_genDom {x : H} (hx : x ∈ genDom U) (t : ℝ) :
    U t x ∈ genDom U ∧ gen U (U t x) = U t (gen U x) := by
  apply mem_genDom_and_gen_eq
  have key : (fun s => U s (U t x)) = fun s => U t (U s x) := by
    funext s
    rw [U_apply_U hadd, U_apply_U hadd, add_comm]
  rw [key, ← ContinuousLinearMap.map_smul]
  have := ((U t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_gen hx)
  simpa [Function.comp_def] using this

omit [CompleteSpace H] in
include hadd in
/-- Differentiability of the orbit at an arbitrary time. -/
theorem hasDerivAt_orbit {x : H} (hx : x ∈ genDom U) (t : ℝ) :
    HasDerivAt (fun s => U s x) (Complex.I • U t (gen U x)) t := by
  have h1 : HasDerivAt (fun s => U s (U t x)) (Complex.I • gen U (U t x)) 0 :=
    hasDerivAt_gen (U_mem_genDom hadd hx t).1
  rw [(U_mem_genDom hadd hx t).2] at h1
  have h2 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h1' : HasDerivAt (fun s => U s (U t x)) (Complex.I • U t (gen U x)) (t - t) := by
    rw [sub_self]; exact h1
  have h3 := HasDerivAt.scomp (𝕜 := ℝ) (h := fun s : ℝ => s - t) (x := t) h1' h2
  have key : ((fun s => U s (U t x)) ∘ fun s : ℝ => s - t) = fun s => U s x := by
    funext s
    simp only [Function.comp_apply]
    rw [U_apply_U hadd, sub_add_cancel]
  rw [key] at h3
  simpa using h3

omit [CompleteSpace H] in
include h0 hnorm in
/-- The generator is symmetric. -/
theorem gen_symmetric {x y : H} (hx : x ∈ genDom U) (hy : y ∈ genDom U) :
    inner ℂ (gen U x) y = inner ℂ x (gen U y) := by
  have hconst : HasDerivAt (fun t : ℝ => inner ℂ (U t x) (U t y)) 0 0 := by
    have : (fun t : ℝ => inner ℂ (U t x) (U t y)) = fun _ : ℝ => (inner ℂ x y : ℂ) := by
      funext t; exact inner_U_U hnorm t x y
    rw [this]
    exact hasDerivAt_const _ _
  have hd := (hasDerivAt_gen hx).inner ℂ (hasDerivAt_gen hy)
  have := hconst.unique hd
  rw [h0] at this
  simp only [ContinuousLinearMap.one_apply, inner_smul_right, inner_smul_left,
    Complex.conj_I] at this
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : Complex.I * inner ℂ x (gen U y) = Complex.I * inner ℂ (gen U x) y := by
    linear_combination -this
  exact (mul_left_cancel₀ hI h2).symm

include h0 hadd hcont in
/-- The derivative at `0` of `h ↦ U h (∫ s in 0..a, U s x)`. -/
theorem hasDerivAt_average (x : H) (a : ℝ) :
    HasDerivAt (fun h : ℝ => U h (∫ s in (0:ℝ)..a, U s x)) (U a x - x) 0 := by
  have hcx : Continuous fun s => U s x := hcont x
  have hint : ∀ b c : ℝ, IntervalIntegrable (fun s => U s x) volume b c := fun b c =>
    hcx.intervalIntegrable b c
  set F : ℝ → H := fun u => ∫ s in (0:ℝ)..u, U s x with hF
  have hFderiv : ∀ u : ℝ, HasDerivAt F (U u x) u := fun u =>
    integral_hasDerivAt_right (hint 0 u) (hcx.stronglyMeasurableAtFilter _ _) hcx.continuousAt
  have hfun : (fun h : ℝ => U h (∫ s in (0:ℝ)..a, U s x)) = fun h : ℝ => F (a + h) - F h := by
    funext h
    have h1 : U h (∫ s in (0:ℝ)..a, U s x) = ∫ s in (0:ℝ)..a, U h (U s x) :=
      ((U h).intervalIntegral_comp_comm (hint 0 a)).symm
    have h2 : (∫ s in (0:ℝ)..a, U h (U s x)) = ∫ s in (0:ℝ)..a, U (h + s) x := by
      simp_rw [U_apply_U hadd]
    have h3 : (∫ s in (0:ℝ)..a, U (h + s) x) = ∫ s in (h + 0)..(h + a), U s x :=
      integral_comp_add_left (fun s => U s x) h
    have h4 : F (a + h) - F h = ∫ s in h..(a + h), U s x :=
      integral_interval_sub_left (hint 0 (a + h)) (hint 0 h)
    rw [h1, h2, h3, h4, add_zero, add_comm h a]
  rw [hfun]
  have hA : HasDerivAt (fun h : ℝ => F (a + h)) (U a x) 0 := by
    have h1 : HasDerivAt F (U a x) (a + 0) := by rw [add_zero]; exact hFderiv a
    have h2 : HasDerivAt (fun h : ℝ => a + h) 1 (0 : ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add a
    simpa using HasDerivAt.scomp (𝕜 := ℝ) (h := fun h : ℝ => a + h) (x := 0) h1 h2
  have hB : HasDerivAt F x 0 := by
    have := hFderiv 0
    rwa [h0, ContinuousLinearMap.one_apply] at this
  exact hA.sub hB

include h0 hadd hcont in
/-- Averages of the orbit lie in the domain of the generator. -/
theorem average_mem_genDom (x : H) (a : ℝ) :
    (∫ s in (0:ℝ)..a, U s x) ∈ genDom U := by
  refine ⟨-Complex.I • (U a x - x), ?_⟩
  have := hasDerivAt_average h0 hadd hcont x a
  rwa [smul_smul, show Complex.I * -Complex.I = 1 by simp [Complex.I_mul_I], one_smul]

include h0 hadd hcont in
/-- The domain of the generator is dense. -/
theorem dense_genDom : Dense (genDom U : Set H) := by
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hcx : Continuous fun s => U s x := hcont x
  have hint : ∀ b c : ℝ, IntervalIntegrable (fun s => U s x) volume b c := fun b c =>
    hcx.intervalIntegrable b c
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousAt_iff.1 (hcx.continuousAt (x := (0:ℝ))) (ε / 2) (by positivity)
  set a : ℝ := δ / 2 with ha
  have ha0 : 0 < a := by positivity
  refine ⟨((a : ℂ)⁻¹ • (∫ s in (0:ℝ)..a, U s x) : H), ?_, ?_⟩
  · exact Submodule.smul_mem _ _ (average_mem_genDom h0 hadd hcont x a)
  · have hane : (a : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt ha0
    have hsplit : (∫ s in (0:ℝ)..a, U s x) - (a : ℂ) • x = ∫ s in (0:ℝ)..a, (U s x - x) := by
      rw [intervalIntegral.integral_sub (hint 0 a) (intervalIntegrable_const)]
      have : (∫ _s in (0:ℝ)..a, x) = (a - 0) • x := intervalIntegral.integral_const x
      rw [this]
      congr 1
      simp
    have hbound : ‖∫ s in (0:ℝ)..a, (U s x - x)‖ ≤ (ε / 2) * |a - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro s hs
      rw [Set.uIoc_of_le ha0.le] at hs
      have hds : dist s 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]
        exact lt_of_le_of_lt hs.2 (by rw [ha]; linarith)
      have := hball hds
      rw [h0] at this
      simpa [dist_eq_norm] using this.le
    have hkey : (a : ℂ)⁻¹ • (∫ s in (0:ℝ)..a, U s x) - x
        = (a : ℂ)⁻¹ • ((∫ s in (0:ℝ)..a, U s x) - (a : ℂ) • x) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hane, one_smul]
    rw [dist_comm, dist_eq_norm, hkey, hsplit, norm_smul]
    have hnorm_inv : ‖(a : ℂ)⁻¹‖ = a⁻¹ := by
      simp [abs_of_pos ha0]
    rw [hnorm_inv]
    have : a⁻¹ * ‖∫ s in (0:ℝ)..a, (U s x - x)‖ ≤ a⁻¹ * ((ε / 2) * |a - 0|) := by
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    have hfin : a⁻¹ * ((ε / 2) * |a - 0|) = ε / 2 := by
      rw [sub_zero, abs_of_pos ha0]
      field_simp
    calc a⁻¹ * ‖∫ s in (0:ℝ)..a, (U s x - x)‖ ≤ a⁻¹ * ((ε / 2) * |a - 0|) := this
      _ = ε / 2 := hfin
      _ < ε := by linarith

include h0 hadd hnorm hcont in
/-- Self-adjointness: any vector in the domain of the adjoint is in the domain of the
generator. -/
theorem genDom_of_adjoint {y z : H}
    (hyz : ∀ x ∈ genDom U, inner ℂ (gen U x) y = inner ℂ x z) :
    y ∈ genDom U ∧ gen U y = z := by
  set w : ℝ → H := fun s => (-Complex.I) • U (-s) z with hw
  have hwcont : Continuous w := by
    have : Continuous fun s : ℝ => U (-s) z := (hcont z).comp continuous_neg
    exact this.const_smul _
  have hwint : ∀ b c : ℝ, IntervalIntegrable w volume b c := fun b c =>
    hwcont.intervalIntegrable b c
  set W : ℝ → H := fun t => ∫ s in (0:ℝ)..t, w s with hW
  -- Step 1: the weak identity, tested against the (dense) domain
  have step1 : ∀ x ∈ genDom U, ∀ t : ℝ, inner ℂ x (U (-t) y - y) = inner ℂ x (W t) := by
    intro x hx t
    have hderiv : ∀ s : ℝ, HasDerivAt (fun r : ℝ => (inner ℂ (U r x) y : ℂ))
        (inner ℂ x (w s)) s := by
      intro s
      have h1 := (hasDerivAt_orbit hadd hx s).inner ℂ (hasDerivAt_const s y)
      have h2 : (inner ℂ (U s x) (0 : H) : ℂ) + inner ℂ (Complex.I • U s (gen U x)) y
          = inner ℂ x (w s) := by
        rw [inner_zero_right, zero_add, inner_smul_left, Complex.conj_I,
          (U_mem_genDom hadd hx s).2.symm, hyz _ (U_mem_genDom hadd hx s).1,
          hw]
        simp only [inner_smul_right]
        rw [inner_U_left h0 hadd hnorm]
      rwa [h2] at h1
    have hfint : IntervalIntegrable (fun s : ℝ => (inner ℂ x (w s) : ℂ)) volume 0 t := by
      exact (continuous_const.inner hwcont).intervalIntegrable 0 t
    have hsub : (∫ s in (0:ℝ)..t, (inner ℂ x (w s) : ℂ))
        = (inner ℂ (U t x) y : ℂ) - inner ℂ (U 0 x) y :=
      integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) hfint
    have hpull : (∫ s in (0:ℝ)..t, (inner ℂ x (w s) : ℂ)) = inner ℂ x (W t) := by
      have := (innerSL ℂ x).intervalIntegral_comp_comm (a := (0:ℝ)) (b := t) (hwint 0 t)
      simpa [hW] using this
    rw [inner_sub_right, ← hpull, hsub, h0, ContinuousLinearMap.one_apply,
      inner_U_left h0 hadd hnorm]
  -- Step 2: hence the strong identity, by density
  have step2 : ∀ t : ℝ, U (-t) y - y = W t := by
    intro t
    refine (dense_genDom h0 hadd hcont).eq_of_inner_right ?_
    rintro ⟨x, hx⟩
    exact step1 x hx t
  -- Step 3: differentiate at `t = 0`
  have hWderiv : HasDerivAt W (w 0) 0 :=
    integral_hasDerivAt_right (hwint 0 0) (hwcont.stronglyMeasurableAtFilter _ _)
      hwcont.continuousAt
  have hgderiv : HasDerivAt (fun t : ℝ => U (-t) y) (w 0) 0 := by
    have hfun : (fun t : ℝ => U (-t) y) = fun t : ℝ => y + W t := by
      funext t
      rw [← step2 t]
      abel
    rw [hfun]
    simpa using hWderiv.const_add y
  have hw0 : w 0 = (-Complex.I) • z := by
    rw [hw]
    simp only [neg_zero]
    rw [h0, ContinuousLinearMap.one_apply]
  rw [hw0] at hgderiv
  refine mem_genDom_and_gen_eq ?_
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).neg
  have hg' : HasDerivAt (fun t : ℝ => U (-t) y) ((-Complex.I) • z) (-(0:ℝ)) := by
    rw [neg_zero]; exact hgderiv
  have hcomp := HasDerivAt.scomp (𝕜 := ℝ) (h := fun t : ℝ => -t) (x := (0:ℝ)) hg' hneg
  have hfun2 : ((fun t : ℝ => U (-t) y) ∘ fun t : ℝ => -t) = fun t : ℝ => U t y := by
    funext t; simp
  rw [hfun2] at hcomp
  have hsmul : (-1 : ℝ) • ((-Complex.I) • z) = Complex.I • z := by
    rw [neg_one_smul, ← neg_smul, neg_neg]
  rwa [hsmul] at hcomp

end Generator

end

/-- **Stone's theorem** (self-adjointness of the generator).

Let `U : ℝ → H →L[ℂ] H` be a strongly continuous one-parameter unitary group on a complex
Hilbert space `H`.  Then its generator `A`, defined on
`D = {x | t ↦ U t x is differentiable at 0}` by `(d/dt) U t x |_{t = 0} = I • A x`
(i.e. `U t = exp (i t A)`), is a densely defined, linear, self-adjoint operator:

* `D` is a dense linear subspace;
* `A` is linear on `D`;
* `A` is symmetric: `⟪A x, y⟫ = ⟪x, A y⟫` for `x, y ∈ D`;
* `A` is maximal symmetric in the strong sense that `A* = A`: whenever `y, z` satisfy
  `⟪A x, y⟫ = ⟪x, z⟫` for all `x ∈ D`, then already `y ∈ D` and `A y = z`.
-/
theorem stone_generator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (h0 : U 0 = 1)
    (hadd : ∀ s t, U (s + t) = (U s).comp (U t)) (hnorm : ∀ t x, ‖U t x‖ = ‖x‖)
    (hcont : ∀ x : H, Continuous fun t => U t x) :
    ∃ (D : Submodule ℂ H) (A : H → H),
      -- `D` is the domain of the generator
      (∀ x, x ∈ D ↔ ∃ z, HasDerivAt (fun t => U t x) (Complex.I • z) 0) ∧
      -- `A` implements the derivative on `D`
      (∀ x ∈ D, HasDerivAt (fun t => U t x) (Complex.I • A x) 0) ∧
      -- `D` is dense
      Dense (D : Set H) ∧
      -- `A` is linear on `D`
      (∀ (c : ℂ), ∀ x ∈ D, ∀ y ∈ D, A (c • x + y) = c • A x + A y) ∧
      -- `A` is symmetric
      (∀ x ∈ D, ∀ y ∈ D, inner ℂ (A x) y = inner ℂ x (A y)) ∧
      -- `A` is self-adjoint: the domain of the adjoint is contained in `D`
      (∀ y z : H, (∀ x ∈ D, inner ℂ (A x) y = inner ℂ x z) → y ∈ D ∧ A y = z) := by
  refine ⟨genDom U, gen U, fun x => Iff.rfl, fun x hx => hasDerivAt_gen hx,
    dense_genDom h0 hadd hcont, ?_, fun x hx y hy => gen_symmetric h0 hnorm hx hy,
    fun y z hyz => genDom_of_adjoint h0 hadd hnorm hcont hyz⟩
  intro c x hx y hy
  refine gen_eq ?_
  have hfun : (fun t => U t (c • x + y)) = fun t => c • U t x + U t y := by
    funext t; simp
  rw [hfun, smul_add, smul_comm]
  exact ((hasDerivAt_gen hx).const_smul c).add (hasDerivAt_gen hy)

/-- Sanity check: the hypotheses of `stone_generator` are satisfiable (they hold for the
unitary group `U t = e^{i t}` on `H = ℂ`), so the theorem is not vacuous. -/
example : ∃ (U : ℝ → ℂ →L[ℂ] ℂ), (U 0 = 1) ∧ (∀ s t, U (s + t) = (U s).comp (U t)) ∧
    (∀ t x, ‖U t x‖ = ‖x‖) ∧ (∀ x : ℂ, Continuous fun t => U t x) := by
  refine ⟨fun t => (Complex.exp (t * Complex.I)) • (1 : ℂ →L[ℂ] ℂ), by simp, ?_, ?_, ?_⟩
  · intro s t
    ext
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, Complex.ofReal_add,
      mul_one]
    rw [← Complex.exp_add]
    ring_nf
  · intro t x
    simp [Complex.norm_exp]
  · intro x
    have : Continuous fun t : ℝ => Complex.exp (t * Complex.I) * x := by fun_prop
    simpa using this

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

