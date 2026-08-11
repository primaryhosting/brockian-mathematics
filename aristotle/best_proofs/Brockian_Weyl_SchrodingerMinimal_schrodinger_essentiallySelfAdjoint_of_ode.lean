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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/
def IsTestFunction (f : ℝ → ℂ) : Prop := ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f

/-- The Schrödinger differential expression `(τ f)(x) = -f''(x) + V₀ * f(x)`
with constant potential `V₀`. The *minimal* Schrödinger operator is `τ` restricted to
test functions, viewed as an unbounded operator on `L²(ℝ)`. -/
noncomputable def schrodingerExpr (V₀ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (deriv f) x + (V₀ : ℂ) * f x

/-! ## A one-dimensional ODE input: bounded solutions for non-real spectral parameter -/

private theorem exp_bound_zero {A C a : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ t → A * Real.exp (a * t) ≤ C) : A = 0 := by
  by_contra hne
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hne)
  have h1 : Tendsto (fun t : ℝ => a * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha Filter.tendsto_id
  have h2 : Tendsto (fun t : ℝ => A * Real.exp (a * t)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hApos (Real.tendsto_exp_atTop.comp h1)
  obtain ⟨t, ht, ht0⟩ := ((h2.eventually_gt_atTop C).and (eventually_ge_atTop 0)).exists
  exact absurd (h t ht0) (not_le.2 ht)

private theorem exp_bound_zero' {A C a : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (h : ∀ t : ℝ, t ≤ 0 → A * Real.exp (-(a * t)) ≤ C) : A = 0 := by
  apply exp_bound_zero ha hA (C := C)
  intro t ht
  simpa using h (-t) (by linarith)

/-- For a `C²` solution of `y'' = c y`, the combination `y' + λ y` (with `λ² = c`)
is an exponential. -/
private theorem sol_formula {c lam : ℂ} (hlam : lam ^ 2 = c) {y : ℝ → ℂ} (hy : ContDiff ℝ 2 y)
    (hode : ∀ t, deriv (deriv y) t = c * y t) :
    ∀ t : ℝ, deriv y t + lam * y t = (deriv y 0 + lam * y 0) * Complex.exp (lam * t) := by
  have hdy : Differentiable ℝ y := hy.differentiable (by norm_num)
  have hdy' : Differentiable ℝ (deriv y) := ContDiff.differentiable_deriv_two hy
  set w : ℝ → ℂ := fun t => deriv y t + lam * y t with hw
  have hwd : ∀ t : ℝ, HasDerivAt w (lam * w t) t := by
    intro t
    have h1 : HasDerivAt (deriv y) (deriv (deriv y) t) t := (hdy' t).hasDerivAt
    have h2 : HasDerivAt y (deriv y t) t := (hdy t).hasDerivAt
    have h3 := h1.add (h2.const_mul lam)
    rw [hode t] at h3
    convert h3 using 1
    rw [hw]
    ring_nf
    rw [← hlam]; ring
  have hgd : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => w t * Complex.exp (-(lam * t))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(lam * t)))
        (-lam * Complex.exp (-(lam * t))) t := by
      have h0 : HasDerivAt (fun t : ℝ => -(lam * (t : ℂ))) (-lam) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul lam).neg
      simpa [mul_comm] using h0.cexp
    have h2 := (hwd t).mul h1
    convert h2 using 1
    ring
  intro t
  have h0 : w t * Complex.exp (-(lam * t)) = w 0 * Complex.exp (-(lam * (0 : ℝ))) :=
    is_const_of_deriv_eq_zero (fun x => (hgd x).differentiableAt) (fun x => (hgd x).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, mul_one] at h0
  have key : w t = w t * Complex.exp (-(lam * t)) * Complex.exp (lam * t) := by
    rw [mul_assoc, ← Complex.exp_add]; simp
  rw [h0] at key
  simpa [hw] using key

/-- **ODE input.** A bounded classical solution of `y'' = c y` with `c` non-real vanishes.
This is the limit-point mechanism: for non-real spectral parameter both exponential
solutions blow up at one of the two ends of the line. -/
theorem bounded_ode_solution_eq_zero {c : ℂ} (hc : c.im ≠ 0) {y : ℝ → ℂ} (hy : ContDiff ℝ 2 y)
    (hode : ∀ t, deriv (deriv y) t = c * y t) {M : ℝ} (hbdd : ∀ t, ‖y t‖ ≤ M) :
    ∀ t, y t = 0 := by
  obtain ⟨lam, hlam, hlamre⟩ : ∃ lam : ℂ, lam ^ 2 = c ∧ 0 < lam.re := by
    obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by norm_num)
    have hre : l.re ≠ 0 := by
      intro h; apply hc; rw [← hl]; simp [pow_two, Complex.mul_im, h]
    rcases lt_or_gt_of_ne hre with h | h
    · exact ⟨-l, by rw [neg_pow]; simpa using hl, by simpa using h⟩
    · exact ⟨l, hl, h⟩
  have hlamne : lam ≠ 0 := by intro h; rw [h] at hlamre; simp at hlamre
  have h1 := sol_formula hlam hy hode
  have h2 := sol_formula (c := c) (lam := -lam) (by rw [neg_pow]; simpa using hlam) hy hode
  have hy2 : ∀ t : ℝ, 2 * lam * y t
      = (deriv y 0 + lam * y 0) * Complex.exp (lam * t)
        - (deriv y 0 + -lam * y 0) * Complex.exp (-lam * t) := by
    intro t; linear_combination h1 t - h2 t
  have hnormexp : ∀ t : ℝ, ‖Complex.exp (lam * t)‖ = Real.exp (lam.re * t) := by
    intro t; rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hnormexp' : ∀ t : ℝ, ‖Complex.exp (-lam * t)‖ = Real.exp (-(lam.re * t)) := by
    intro t; rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hbdd 0)
  have hn2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  set A := deriv y 0 + lam * y 0 with hAdef
  set B := deriv y 0 + -lam * y 0 with hBdef
  have hA : A = 0 := by
    rw [← norm_eq_zero]
    apply exp_bound_zero hlamre (norm_nonneg A) (C := 2 * ‖lam‖ * M + ‖B‖)
    intro t ht
    have hb1 : ‖A * Complex.exp (lam * t)‖
        ≤ ‖2 * lam * y t‖ + ‖B * Complex.exp (-lam * t)‖ := by
      calc ‖A * Complex.exp (lam * t)‖
          = ‖2 * lam * y t + B * Complex.exp (-lam * t)‖ := by rw [hy2 t]; ring_nf
        _ ≤ _ := norm_add_le _ _
    simp only [norm_mul, hnormexp, hnormexp', hn2] at hb1
    have h4 : Real.exp (-(lam.re * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.2; nlinarith
    nlinarith [norm_nonneg B, norm_nonneg lam, hbdd t, Real.exp_pos (-(lam.re * t))]
  have hB : B = 0 := by
    rw [← norm_eq_zero]
    apply exp_bound_zero' hlamre (norm_nonneg B) (C := 2 * ‖lam‖ * M)
    intro t ht
    have hb1 : ‖B * Complex.exp (-lam * t)‖ ≤ ‖2 * lam * y t‖ := by
      have hz : B * Complex.exp (-lam * t) = -(2 * lam * y t) := by rw [hy2 t, hA]; ring
      rw [hz, norm_neg]
    simp only [norm_mul, hnormexp', hn2] at hb1
    nlinarith [norm_nonneg lam, hbdd t, norm_nonneg (y t)]
  intro t
  have h3 := hy2 t
  rw [hA, hB] at h3
  simp at h3
  rcases h3 with h | h
  · exact absurd h (by simpa using hlamne)
  · exact h

/-! ## Elementary calculus and integration facts -/

private theorem integral_deriv_eq_zero {h : ℝ → ℂ} (hc : ContDiff ℝ 1 h)
    (hcs : HasCompactSupport h) : ∫ x, deriv h x = 0 := by
  have hint : Integrable (deriv h) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hc.continuous_deriv le_rfl
    · exact hcs.deriv
  have h1 : (∫ x in Set.Iic (0:ℝ), deriv h x) + ∫ x in Set.Ioi (0:ℝ), deriv h x
      = ∫ x, deriv h x :=
    intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn
  rw [← h1, hcs.integral_Iic_deriv_eq hc 0, hcs.integral_Ioi_deriv_eq hc 0]
  ring

private theorem deriv_comp_const_sub {ρ : ℝ → ℂ} (hρ : Differentiable ℝ ρ) (t : ℝ) :
    deriv (fun x => ρ (t - x)) = fun x => -deriv ρ (t - x) := by
  funext x
  have h1 : HasDerivAt (fun x : ℝ => t - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub t
  have h2 := (hρ (t - x)).hasDerivAt.scomp x h1
  simpa using h2.deriv

private theorem integrable_mul_test {F g : ℝ → ℂ} (hF : LocallyIntegrable F volume)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Integrable (fun x => F x * g x) volume := by
  have h := hF.integrable_smul_left_of_hasCompactSupport hg hgc
  refine h.congr (Filter.Eventually.of_forall ?_)
  intro x
  simp [smul_eq_mul, mul_comm]

/-- Cauchy–Schwarz: the convolution of an `L²` function with a test function is bounded. -/
private theorem conv_bounded {u ρ : ℝ → ℂ} (hu : MemLp u 2 volume) (hρc : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (t : ℝ) :
    ‖∫ x, (starRingEnd ℂ) (u x) * ρ (t - x)‖
      ≤ (∫ x, ‖u x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (∫ x, ‖ρ x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hρt : MemLp (fun x => ρ (t - x)) (ENNReal.ofReal 2) volume := by
    apply Continuous.memLp_of_hasCompactSupport
    · exact hρc.comp (continuous_const.sub continuous_id)
    · exact hcρ.comp_homeomorph (Homeomorph.subLeft t)
  have hu2 : MemLp (fun x => (starRingEnd ℂ) (u x)) (ENNReal.ofReal 2) volume := by
    have hu' : MemLp u (ENNReal.ofReal 2) volume := by simpa using hu
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hu'.1, ?_⟩
    have : eLpNorm (fun x => (starRingEnd ℂ) (u x)) (ENNReal.ofReal 2) volume
        = eLpNorm u (ENNReal.ofReal 2) volume := by
      apply eLpNorm_congr_norm_ae
      filter_upwards with x
      simp
    rw [this]
    exact hu'.2
  calc ‖∫ x, (starRingEnd ℂ) (u x) * ρ (t - x)‖
      ≤ ∫ x, ‖(starRingEnd ℂ) (u x) * ρ (t - x)‖ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖(starRingEnd ℂ) (u x)‖ * ‖ρ (t - x)‖ := by simp
    _ ≤ (∫ x, ‖(starRingEnd ℂ) (u x)‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
          * (∫ x, ‖ρ (t - x)‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hu2 hρt
    _ = _ := by
        congr 1
        · simp
        · congr 1
          exact integral_sub_left_eq_self (fun x => ‖ρ x‖ ^ (2 : ℝ)) volume t

/-! ## Symmetry of the minimal operator -/

/-- The minimal Schrödinger operator is symmetric on test functions. -/
theorem schrodinger_symmetric (V₀ : ℝ) {f g : ℝ → ℂ} (hf : IsTestFunction f)
    (hg : IsTestFunction g) :
    ∫ x, (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x
      = ∫ x, (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x := by
  obtain ⟨hfs, hfc⟩ := hf
  obtain ⟨hgs, hgc⟩ := hg
  have hfs' : ContDiff ℝ (⊤ : ℕ∞) (deriv f) := by simpa using hfs.iterate_deriv 1
  have hgs' : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := by simpa using hgs.iterate_deriv 1
  have hfs'' : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv f)) := by simpa using hfs.iterate_deriv 2
  have hgs'' : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv g)) := by simpa using hgs.iterate_deriv 2
  have hf1 : Differentiable ℝ f := hfs.differentiable (by simp)
  have hg1 : Differentiable ℝ g := hgs.differentiable (by simp)
  have hf1' : Differentiable ℝ (deriv f) := hfs'.differentiable (by simp)
  have hg1' : Differentiable ℝ (deriv g) := hgs'.differentiable (by simp)
  have hconjf : HasCompactSupport (fun x => (starRingEnd ℂ) (f x)) :=
    hfc.comp_left (g := fun z : ℂ => (starRingEnd ℂ) z) (by simp)
  -- the boundary term `conj f' * g - conj f * g'` is a compactly supported `C¹` function
  set h : ℝ → ℂ := fun x => (starRingEnd ℂ) (deriv f x) * g x
      - (starRingEnd ℂ) (f x) * deriv g x with hh
  have hderiv : ∀ x, HasDerivAt h
      ((starRingEnd ℂ) (deriv (deriv f) x) * g x
        - (starRingEnd ℂ) (f x) * deriv (deriv g) x) x := by
    intro x
    have a1 : HasDerivAt (fun y => (starRingEnd ℂ) (deriv f y))
        ((starRingEnd ℂ) (deriv (deriv f) x)) x := ((hf1' x).hasDerivAt).star
    have a2 : HasDerivAt g (deriv g x) x := (hg1 x).hasDerivAt
    have a3 : HasDerivAt (fun y => (starRingEnd ℂ) (f y)) ((starRingEnd ℂ) (deriv f x)) x :=
      ((hf1 x).hasDerivAt).star
    have a4 : HasDerivAt (deriv g) (deriv (deriv g) x) x := (hg1' x).hasDerivAt
    have a5 := (a1.mul a2).sub (a3.mul a4)
    convert a5 using 1
    ring
  have hcont : ContDiff ℝ 1 h := by
    have c1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => (starRingEnd ℂ) (deriv f y)) :=
      Complex.conjCLE.contDiff.comp hfs'
    have c2 : ContDiff ℝ (⊤ : ℕ∞) (fun y => (starRingEnd ℂ) (f y)) :=
      Complex.conjCLE.contDiff.comp hfs
    exact ((c1.mul hgs).sub (c2.mul hgs')).of_le (by exact_mod_cast le_top)
  have hcs : HasCompactSupport h := HasCompactSupport.sub hgc.mul_left hgc.deriv.mul_left
  have hzero : ∫ x, ((starRingEnd ℂ) (deriv (deriv f) x) * g x
      - (starRingEnd ℂ) (f x) * deriv (deriv g) x) = 0 := by
    have hd : deriv h = fun x => (starRingEnd ℂ) (deriv (deriv f) x) * g x
        - (starRingEnd ℂ) (f x) * deriv (deriv g) x := funext fun x => (hderiv x).deriv
    rw [← hd]
    exact integral_deriv_eq_zero hcont hcs
  have hint1 : Integrable (fun x => (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_conj.comp
        (hfs''.continuous.neg.add (continuous_const.mul hfs.continuous))).mul hg1.continuous
    · exact hgc.mul_left
  have hint2 : Integrable (fun x => (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (Complex.continuous_conj.comp hfs.continuous).mul
        (hgs''.continuous.neg.add (continuous_const.mul hgs.continuous))
    · exact hconjf.mul_right
  have hfinal : (∫ x, (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x)
      - ∫ x, (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x = 0 := by
    rw [← integral_sub hint1 hint2]
    have hcongr : (fun x => (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x
          - (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x)
        = fun x => -((starRingEnd ℂ) (deriv (deriv f) x) * g x
          - (starRingEnd ℂ) (f x) * deriv (deriv g) x) := by
      funext x
      simp only [schrodingerExpr, map_add, map_neg, map_mul, Complex.conj_ofReal]
      ring
    rw [hcongr, integral_neg, hzero, neg_zero]
  exact sub_eq_zero.mp hfinal

/-! ## The deficiency spaces are trivial -/

/-- **Main analytic step (the discharged ODE hypothesis).**
If `u ∈ L²(ℝ)` is orthogonal to the range of `τ - z` on test functions, with `z` non-real,
then `u = 0` almost everywhere. -/
theorem weak_solution_eq_zero (V₀ : ℝ) {z : ℂ} (hz : z.im ≠ 0) {u : ℝ → ℂ}
    (hu : MemLp u 2 volume)
    (hweak : ∀ f : ℝ → ℂ, IsTestFunction f →
      ∫ x, (starRingEnd ℂ) (u x) * (schrodingerExpr V₀ f x - z * f x) = 0) :
    u =ᵐ[volume] 0 := by
  set F : ℝ → ℂ := fun x => (starRingEnd ℂ) (u x) with hFdef
  have hFmem : MemLp F 2 volume := by
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hu.1, ?_⟩
    have hnorm : eLpNorm F 2 volume = eLpNorm u 2 volume := by
      apply eLpNorm_congr_norm_ae; filter_upwards with x; simp [hFdef]
    rw [hnorm]; exact hu.2
  have hFloc : LocallyIntegrable F volume := hFmem.locallyIntegrable one_le_two
  set L := ContinuousLinearMap.mul ℝ ℂ with hL
  -- For every test function `ρ`, the smooth function `F ⋆ ρ` is a bounded solution of the
  -- ODE `y'' = (V₀ - z) y`, hence vanishes identically.
  have key : ∀ ρ : ℝ → ℂ, IsTestFunction ρ → ∀ t : ℝ, (F ⋆[L, volume] ρ) t = 0 := by
    rintro ρ ⟨hρs, hρc⟩ t₀
    have hρ1 : Differentiable ℝ ρ := hρs.differentiable (by simp)
    have hρs' : ContDiff ℝ (⊤ : ℕ∞) (deriv ρ) := by simpa using hρs.iterate_deriv 1
    have hρ1' : Differentiable ℝ (deriv ρ) := hρs'.differentiable (by simp)
    have hd1 : deriv (F ⋆[L, volume] ρ) = F ⋆[L, volume] (deriv ρ) := by
      funext t
      exact (hρc.hasDerivAt_convolution_right L hFloc
        (hρs.of_le (by exact_mod_cast le_top)) t).deriv
    have hd2 : deriv (deriv (F ⋆[L, volume] ρ)) = F ⋆[L, volume] (deriv (deriv ρ)) := by
      rw [hd1]
      funext t
      exact ((hρc.deriv).hasDerivAt_convolution_right L hFloc
        (hρs'.of_le (by exact_mod_cast le_top)) t).deriv
    have hy2 : ContDiff ℝ 2 (F ⋆[L, volume] ρ) :=
      (hρc.contDiff_convolution_right L hFloc hρs).of_le ENat.LEInfty.out
    have hode : ∀ t : ℝ, deriv (deriv (F ⋆[L, volume] ρ)) t
        = ((V₀ : ℂ) - z) * (F ⋆[L, volume] ρ) t := by
      intro t
      have htest : IsTestFunction (fun x => ρ (t - x)) :=
        ⟨hρs.comp (contDiff_const.sub contDiff_id),
         hρc.comp_homeomorph (Homeomorph.subLeft t)⟩
      have hw := hweak _ htest
      have hsec : deriv (deriv (fun x => ρ (t - x))) = fun x => deriv (deriv ρ) (t - x) := by
        rw [deriv_comp_const_sub hρ1 t, deriv.fun_neg', deriv_comp_const_sub hρ1' t]
        funext x; simp
      simp only [schrodingerExpr, hsec] at hw
      have hint1 : Integrable (fun x => F x * deriv (deriv ρ) (t - x)) volume := by
        apply integrable_mul_test hFloc
        · exact (hρs'.continuous_deriv (by exact_mod_cast le_top)).comp
            (continuous_const.sub continuous_id)
        · exact (hρc.deriv.deriv).comp_homeomorph (Homeomorph.subLeft t)
      have hint2 : Integrable (fun x => F x * ρ (t - x)) volume := by
        apply integrable_mul_test hFloc
        · exact hρ1.continuous.comp (continuous_const.sub continuous_id)
        · exact hρc.comp_homeomorph (Homeomorph.subLeft t)
      have hsplit : (∫ x, (-(F x * deriv (deriv ρ) (t - x))
            + ((V₀ : ℂ) - z) * (F x * ρ (t - x)))) = 0 := by
        rw [← hw]; congr 1; funext x; ring
      have hadd := integral_add (μ := volume)
        (f := fun x => -(F x * deriv (deriv ρ) (t - x)))
        (g := fun x => ((V₀ : ℂ) - z) * (F x * ρ (t - x))) hint1.neg (hint2.const_mul _)
      rw [hadd, integral_neg, integral_const_mul] at hsplit
      have e1 : (F ⋆[L, volume] (deriv (deriv ρ))) t = ∫ x, F x * deriv (deriv ρ) (t - x) := rfl
      have e2 : (F ⋆[L, volume] ρ) t = ∫ x, F x * ρ (t - x) := rfl
      rw [hd2, e1, e2]
      linear_combination -hsplit
    have hbdd : ∀ t : ℝ, ‖(F ⋆[L, volume] ρ) t‖
        ≤ (∫ x, ‖u x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (∫ x, ‖ρ x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
      fun t => conv_bounded hu hρ1.continuous hρc t
    exact bounded_ode_solution_eq_zero (by simp [Complex.sub_im, hz]) hy2 hode hbdd t₀
  have hFae : ∀ᵐ x ∂volume, F x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hFloc
    intro g hg hgc
    have hρtest : IsTestFunction (fun x => ((g (-x) : ℝ) : ℂ)) := by
      constructor
      · exact Complex.ofRealCLM.contDiff.comp (hg.comp contDiff_neg)
      · apply HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) _ (by simp)
        exact hgc.comp_homeomorph (Homeomorph.neg ℝ)
    have hk := key _ hρtest 0
    have e : (F ⋆[L, volume] (fun x => ((g (-x) : ℝ) : ℂ))) 0 = ∫ x, F x * (g x : ℂ) := by
      simp [convolution, hL]
    rw [e] at hk
    rw [← hk]
    congr 1
    funext x
    simp [Complex.real_smul, mul_comm]
  filter_upwards [hFae] with x hx
  have hux : u x = (starRingEnd ℂ) (F x) := by simp [hFdef]
  rw [hux, hx]; simp

/-! ## Linearity of the minimal operator -/

theorem isTestFunction_add {f g : ℝ → ℂ} (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => f x + g x) := ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem isTestFunction_smul (c : ℂ) {f : ℝ → ℂ} (hf : IsTestFunction f) :
    IsTestFunction (fun x => c * f x) := ⟨contDiff_const.mul hf.1, hf.2.mul_left⟩

theorem schrodingerExpr_add (V₀ : ℝ) {f g : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    schrodingerExpr V₀ (fun x => f x + g x)
      = fun x => schrodingerExpr V₀ f x + schrodingerExpr V₀ g x := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
  have hf1' : Differentiable ℝ (deriv f) :=
    (by simpa using hf.iterate_deriv 1 : ContDiff ℝ (⊤ : ℕ∞) (deriv f)).differentiable (by simp)
  have hg1' : Differentiable ℝ (deriv g) :=
    (by simpa using hg.iterate_deriv 1 : ContDiff ℝ (⊤ : ℕ∞) (deriv g)).differentiable (by simp)
  have h1 : deriv (fun x => f x + g x) = fun x => deriv f x + deriv g x :=
    funext fun x => deriv_add (hf1 x) (hg1 x)
  have h2 : deriv (fun x => deriv f x + deriv g x)
      = fun x => deriv (deriv f) x + deriv (deriv g) x :=
    funext fun x => deriv_add (hf1' x) (hg1' x)
  funext x
  simp only [schrodingerExpr, h1, h2]
  ring

theorem schrodingerExpr_smul (V₀ : ℝ) (c : ℂ) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    schrodingerExpr V₀ (fun x => c * f x) = fun x => c * schrodingerExpr V₀ f x := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hf1' : Differentiable ℝ (deriv f) :=
    (by simpa using hf.iterate_deriv 1 : ContDiff ℝ (⊤ : ℕ∞) (deriv f)).differentiable (by simp)
  have h1 : deriv (fun x => c * f x) = fun x => c * deriv f x :=
    funext fun x => deriv_const_mul c (hf1 x)
  have h2 : deriv (fun x => c * deriv f x) = fun x => c * deriv (deriv f) x :=
    funext fun x => deriv_const_mul c (hf1' x)
  funext x
  simp only [schrodingerExpr, h1, h2]
  ring

/-! ## The range of `τ - z` as a subspace of `L²(ℝ)` -/

open scoped Classical in
/-- The class in `L²(ℝ)` of a function, when the function is square integrable. -/
noncomputable def ccLp (f : ℝ → ℂ) : Lp ℂ 2 (volume : Measure ℝ) :=
  if h : MemLp f 2 volume then h.toLp f else 0

theorem ccLp_of_memLp {f : ℝ → ℂ} (h : MemLp f 2 volume) : ccLp f = h.toLp f := by
  rw [ccLp, dif_pos h]

theorem ccLp_coe {f : ℝ → ℂ} (h : MemLp f 2 volume) : (ccLp f : ℝ → ℂ) =ᵐ[volume] f := by
  rw [ccLp_of_memLp h]; exact h.coeFn_toLp

theorem ccLp_add {f g : ℝ → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ccLp (fun x => f x + g x) = ccLp f + ccLp g := by
  have h1 : (fun x => f x + g x) = f + g := rfl
  rw [h1, ccLp_of_memLp (hf.add hg), ccLp_of_memLp hf, ccLp_of_memLp hg, ← MemLp.toLp_add hf hg]

theorem ccLp_smul (c : ℂ) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ccLp (fun x => c * f x) = c • ccLp f := by
  have h1 : (fun x => c * f x) = c • f := rfl
  rw [h1, ccLp_of_memLp (hf.const_smul c), ccLp_of_memLp hf, ← MemLp.toLp_const_smul c hf]

theorem ccLp_zero : ccLp (fun _ : ℝ => (0 : ℂ)) = 0 := by
  have h : MemLp (fun _ : ℝ => (0 : ℂ)) 2 volume := MemLp.zero'
  rw [ccLp_of_memLp h]
  apply Lp.ext
  filter_upwards [h.coeFn_toLp, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x h1 h2
  rw [h1, h2]
  rfl

theorem memLp_expr (V₀ : ℝ) (z : ℂ) {f : ℝ → ℂ} (hf : IsTestFunction f) :
    MemLp (fun x => schrodingerExpr V₀ f x - z * f x) 2 volume := by
  obtain ⟨hs, hc⟩ := hf
  have hs'' : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv f)) := by simpa using hs.iterate_deriv 2
  apply Continuous.memLp_of_hasCompactSupport
  · exact (hs''.continuous.neg.add (continuous_const.mul hs.continuous)).sub
      (continuous_const.mul hs.continuous)
  · exact HasCompactSupport.sub (HasCompactSupport.add hc.deriv.deriv.neg hc.mul_left) hc.mul_left

/-- The range of `τ - z` applied to test functions, as a subspace of `L²(ℝ)`. -/
noncomputable def deficiencyRange (V₀ : ℝ) (z : ℂ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) where
  carrier := {v | ∃ f : ℝ → ℂ, IsTestFunction f ∧
    v = ccLp (fun x => schrodingerExpr V₀ f x - z * f x)}
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    refine ⟨fun x => f x + g x, isTestFunction_add hf hg, ?_⟩
    rw [← ccLp_add (memLp_expr V₀ z hf) (memLp_expr V₀ z hg)]
    congr 1
    funext x
    rw [schrodingerExpr_add V₀ hf.1 hg.1]
    ring
  zero_mem' := by
    refine ⟨0, ⟨contDiff_const, by
      simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : ℝ => (0 : ℂ)))⟩, ?_⟩
    have h0 : (fun x : ℝ => schrodingerExpr V₀ (0 : ℝ → ℂ) x - z * (0 : ℝ → ℂ) x)
        = fun _ : ℝ => (0 : ℂ) := by
      funext x; simp [schrodingerExpr]
    rw [h0, ccLp_zero]
  smul_mem' := by
    rintro c a ⟨f, hf, rfl⟩
    refine ⟨fun x => c * f x, isTestFunction_smul c hf, ?_⟩
    rw [← ccLp_smul c (memLp_expr V₀ z hf)]
    congr 1
    funext x
    rw [schrodingerExpr_smul V₀ c hf.1]
    ring

/-- The deficiency space is trivial: nothing in `L²` is orthogonal to the range of `τ - z`. -/
theorem deficiencyRange_orthogonal_eq_bot (V₀ : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (deficiencyRange V₀ z)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hmem : MemLp ((w : ℝ → ℂ)) 2 volume := Lp.memLp w
  have key : ∀ f : ℝ → ℂ, IsTestFunction f →
      ∫ x, (starRingEnd ℂ) ((w : ℝ → ℂ) x) * (schrodingerExpr V₀ f x - z * f x) = 0 := by
    intro f hf
    have h1 : ccLp (fun x => schrodingerExpr V₀ f x - z * f x) ∈ deficiencyRange V₀ z :=
      ⟨f, hf, rfl⟩
    have h2 := (Submodule.mem_orthogonal _ _).1 hw _ h1
    rw [L2.inner_def] at h2
    have h3 : ∫ x, ((w : ℝ → ℂ) x)
        * (starRingEnd ℂ) ((ccLp (fun x => schrodingerExpr V₀ f x - z * f x) : ℝ → ℂ) x) = 0 := by
      rw [← h2]
      apply integral_congr_ae
      filter_upwards with x
      rw [RCLike.inner_apply]
    have h4 : (starRingEnd ℂ) (∫ x, ((w : ℝ → ℂ) x)
        * (starRingEnd ℂ)
          ((ccLp (fun x => schrodingerExpr V₀ f x - z * f x) : ℝ → ℂ) x)) = 0 := by
      rw [h3]; simp
    rw [← integral_conj] at h4
    rw [← h4]
    apply integral_congr_ae
    filter_upwards [ccLp_coe (memLp_expr V₀ z hf)] with x hx
    rw [map_mul, hx]
    simp [mul_comm]
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (weak_solution_eq_zero V₀ hz hmem key)

/-- For non-real `z`, the range of `τ - z` on test functions is dense in `L²(ℝ)`. -/
theorem schrodinger_range_dense (V₀ : ℝ) {z : ℂ} (hz : z.im ≠ 0) {w : ℝ → ℂ}
    (hw : MemLp w 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℂ, IsTestFunction f ∧
      eLpNorm (fun x => w x - (schrodingerExpr V₀ f x - z * f x)) 2 volume < ENNReal.ofReal ε := by
  have hbot := deficiencyRange_orthogonal_eq_bot V₀ hz
  have hclosure : (deficiencyRange V₀ z).topologicalClosure = ⊤ := by
    have h1 : (deficiencyRange V₀ z)ᗮᗮ = (deficiencyRange V₀ z).topologicalClosure :=
      Submodule.orthogonal_orthogonal_eq_closure _
    rw [hbot] at h1
    simpa using h1.symm
  have hdense : Dense ((deficiencyRange V₀ z : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)))
      : Set (Lp ℂ 2 (volume : Measure ℝ))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure
  obtain ⟨v, hvS, hvd⟩ := Metric.mem_closure_iff.1 (hdense (hw.toLp w)) ε hε
  obtain ⟨f, hf, rfl⟩ := hvS
  refine ⟨f, hf, ?_⟩
  have hsub : MemLp (fun x => w x - (schrodingerExpr V₀ f x - z * f x)) 2 volume :=
    hw.sub (memLp_expr V₀ z hf)
  have heq : eLpNorm (fun x => w x - (schrodingerExpr V₀ f x - z * f x)) 2 volume
      = eLpNorm (⇑(hw.toLp w) - ⇑(ccLp (fun x => schrodingerExpr V₀ f x - z * f x))) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [hw.coeFn_toLp, ccLp_coe (memLp_expr V₀ z hf)] with x h1 h2
    simp [h1, h2]
  rw [heq]
  rw [Lp.dist_def] at hvd
  rw [ENNReal.lt_ofReal_iff_toReal_lt]
  · exact hvd
  · rw [← heq]; exact hsub.2.ne

/-! ## The ODE hypothesis, and its discharge -/

/-- The ODE hypothesis on which essential self-adjointness of the minimal Schrödinger
operator rests (the Weyl limit-point condition, in weak form): for non-real spectral
parameter `z`, no nonzero `L²` function solves `-u'' + V₀ u = z u` weakly.  Equivalently,
both deficiency spaces of the minimal operator are trivial. -/
def OdeDeficiencyHypothesis (V₀ : ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ u : ℝ → ℂ, MemLp u 2 volume →
    (∀ f : ℝ → ℂ, IsTestFunction f →
      ∫ x, (starRingEnd ℂ) (u x) * (schrodingerExpr V₀ f x - z * f x) = 0) →
    u =ᵐ[volume] 0

/-- **The ODE hypothesis holds**, for every constant potential. -/
theorem odeDeficiencyHypothesis_holds (V₀ : ℝ) : OdeDeficiencyHypothesis V₀ :=
  fun _ hz _ hu hweak => weak_solution_eq_zero V₀ hz hu hweak

/-! ## Essential self-adjointness -/

/-- **Essential self-adjointness of the minimal Schrödinger operator with constant potential.**

The minimal operator is `τ f = -f'' + V₀ f` acting on smooth compactly supported functions,
viewed as a densely defined operator on `L²(ℝ)`. The theorem states the two halves of the
basic criterion for essential self-adjointness:

* `τ` is symmetric on test functions;
* for every non-real `z`, the range of `τ - z` on test functions is dense in `L²(ℝ)`
  (equivalently, both deficiency spaces are trivial).

The ODE input that used to be assumed — that for non-real spectral parameter no nonzero
`L²` function solves `-u'' + V₀ u = z u` weakly — is discharged in
`Brockian.Weyl.SchrodingerMinimal.weak_solution_eq_zero`, so the statement is unconditional. -/
theorem schrodinger_essentiallySelfAdjoint_of_ode (V₀ : ℝ) :
    (∀ f g : ℝ → ℂ, IsTestFunction f → IsTestFunction g →
        ∫ x, (starRingEnd ℂ) (schrodingerExpr V₀ f x) * g x
          = ∫ x, (starRingEnd ℂ) (f x) * schrodingerExpr V₀ g x)
    ∧ (∀ z : ℂ, z.im ≠ 0 → ∀ w : ℝ → ℂ, MemLp w 2 volume → ∀ ε : ℝ, 0 < ε →
        ∃ f : ℝ → ℂ, IsTestFunction f ∧
          eLpNorm (fun x => w x - (schrodingerExpr V₀ f x - z * f x)) 2 volume
            < ENNReal.ofReal ε) :=
  ⟨fun _ _ hf hg => schrodinger_symmetric V₀ hf hg,
   fun _ hz _ hw _ hε => schrodinger_range_dense V₀ hz hw hε⟩

end Brockian.Weyl.SchrodingerMinimal

