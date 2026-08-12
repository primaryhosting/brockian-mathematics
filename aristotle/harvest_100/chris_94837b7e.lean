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

import Brockian.Weyl.TestFunction

/-!
# The du Bois-Reymond lemmas

A locally integrable function whose distributional derivative vanishes is almost everywhere
constant; a locally integrable function whose distributional second derivative vanishes is
almost everywhere affine.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace Brockian.Weyl.DeficiencyODE

/-! ## The du Bois-Reymond lemmas -/

/-- **du Bois-Reymond lemma.**  A locally integrable function whose distributional derivative
vanishes is almost everywhere constant. -/
theorem ae_eq_const_of_weak_deriv_eq_zero {v : ℝ → ℂ} (hv : LocallyIntegrable v volume)
    (h : ∀ ψ : ℝ → ℝ, IsTestFunction ψ → ∫ x, ((deriv ψ x : ℝ) : ℂ) * v x = 0) :
    ∃ c : ℂ, v =ᵐ[volume] fun _ => c := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_testFunction_integral_eq_one
  set c : ℂ := ∫ x, ((χ x : ℝ) : ℂ) * v x with hc
  refine ⟨c, ?_⟩
  have key : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (v x - c) = 0 := by
    intro ψ h1 h2
    have hψ : IsTestFunction ψ := ⟨h1, h2⟩
    set m : ℝ := ∫ x, ψ x with hm
    set ψ₀ : ℝ → ℝ := fun x => ψ x - m * χ x with hψ₀
    have hψ₀T : IsTestFunction ψ₀ :=
      ⟨h1.sub (contDiff_const.mul hχ.1), h2.sub (hχ.2.mul_left)⟩
    have h0 : ∫ x, ψ₀ x = 0 := by
      rw [hψ₀]
      rw [integral_sub hψ.integrable ((hχ.integrable.const_mul m))]
      rw [integral_const_mul, hχ1, ← hm]
      ring
    obtain ⟨Φ, hΦ, hdΦ⟩ := hψ₀T.exists_primitive h0
    have hkey := h Φ hΦ
    rw [hdΦ] at hkey
    -- expand
    have hmchi : IsTestFunction (fun x => m * χ x) :=
      ⟨contDiff_const.mul hχ.1, hχ.2.mul_left⟩
    have hint1 : Integrable (fun x => ((ψ x : ℝ) : ℂ) * v x) :=
      integrable_ofReal_mul_of_locallyIntegrable hψ hv
    have hint2 : Integrable (fun x => ((m * χ x : ℝ) : ℂ) * v x) :=
      integrable_ofReal_mul_of_locallyIntegrable hmchi hv
    have hsplit : ∫ x, ((ψ₀ x : ℝ) : ℂ) * v x
        = (∫ x, ((ψ x : ℝ) : ℂ) * v x) - ∫ x, ((m * χ x : ℝ) : ℂ) * v x := by
      rw [← integral_sub hint1 hint2]
      apply integral_congr_ae
      filter_upwards with x
      simp only [hψ₀, Complex.ofReal_sub]
      ring
    have hmc : ∫ x, ((m * χ x : ℝ) : ℂ) * v x = (m : ℂ) * c := by
      rw [hc, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Complex.ofReal_mul]
      ring
    rw [hsplit, hmc] at hkey
    -- conclude
    have hcm : ∫ x, ψ x • (v x - c) = (∫ x, ((ψ x : ℝ) : ℂ) * v x) - (m : ℂ) * c := by
      have hint3 : Integrable (fun x => ((ψ x : ℝ) : ℂ) * c) :=
        integrable_ofReal_mul hψ continuous_const
      have : ∫ x, ψ x • (v x - c)
          = (∫ x, ((ψ x : ℝ) : ℂ) * v x) - ∫ x, ((ψ x : ℝ) : ℂ) * c := by
        rw [← integral_sub hint1 hint3]
        apply integral_congr_ae
        filter_upwards with x
        rw [Complex.real_smul]
        ring
      rw [this]
      congr 1
      rw [integral_mul_const, integral_complex_ofReal, ← hm]
    rw [hcm, hkey]
  have hli : LocallyIntegrable (fun x => v x - c) volume :=
    hv.sub (continuous_const.locallyIntegrable)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hli key
  filter_upwards [hae] with x hx
  simpa [sub_eq_zero] using hx

/-- **du Bois-Reymond lemma, second order.**  A locally integrable function whose distributional
second derivative vanishes is almost everywhere affine. -/
theorem ae_eq_affine_of_weak_second_deriv_eq_zero {v : ℝ → ℂ}
    (hv : LocallyIntegrable v volume)
    (h : ∀ φ : ℝ → ℝ, IsTestFunction φ → ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * v x = 0) :
    ∃ a b : ℂ, v =ᵐ[volume] fun x => a + b * x := by
  obtain ⟨χ, hχ, hχ1⟩ := exists_testFunction_integral_eq_one
  set k : ℂ := ∫ x, ((deriv χ x : ℝ) : ℂ) * v x with hk
  have hstep : ∀ ψ : ℝ → ℝ, IsTestFunction ψ →
      ∫ x, ((deriv ψ x : ℝ) : ℂ) * (v x + k * x) = 0 := by
    intro ψ hψ
    set m : ℝ := ∫ x, ψ x with hm
    have hmchi : IsTestFunction (fun x => m * χ x) := ⟨contDiff_const.mul hχ.1, hχ.2.mul_left⟩
    set ψ₀ : ℝ → ℝ := fun x => ψ x - m * χ x with hψ₀
    have hψ₀T : IsTestFunction ψ₀ := ⟨hψ.1.sub hmchi.1, hψ.2.sub hmchi.2⟩
    have h0 : ∫ x, ψ₀ x = 0 := by
      rw [hψ₀, integral_sub hψ.integrable (hχ.integrable.const_mul m), integral_const_mul,
        hχ1, ← hm]
      ring
    obtain ⟨Φ, hΦ, hdΦ⟩ := hψ₀T.exists_primitive h0
    have hdψ : ∀ x, deriv ψ x = deriv (deriv Φ) x + m * deriv χ x := by
      intro x
      have hda : HasDerivAt (fun y => ψ y - m * χ y) (deriv ψ x - m * deriv χ x) x :=
        ((hψ.differentiable x).hasDerivAt).sub
          (HasDerivAt.const_mul m ((hχ.differentiable x).hasDerivAt))
      have h1 : deriv ψ₀ x = deriv ψ x - m * deriv χ x := by rw [hψ₀]; exact hda.deriv
      rw [hdΦ, h1]; ring
    have hd1 : IsTestFunction (deriv ψ) := isTestFunction_deriv hψ
    have i1 : Integrable (fun x => ((deriv ψ x : ℝ) : ℂ) * v x) :=
      integrable_ofReal_mul_of_locallyIntegrable hd1 hv
    have i2 : Integrable (fun x => ((deriv ψ x : ℝ) : ℂ) * (k * (x : ℂ))) :=
      integrable_ofReal_mul hd1 (by fun_prop)
    have hsum : (fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * (v x + k * x))
        = fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * v x + ((deriv ψ x : ℝ) : ℂ) * (k * (x : ℂ)) := by
      funext x; ring
    -- the first integral
    have hA : ∫ x, ((deriv ψ x : ℝ) : ℂ) * v x = (m : ℂ) * k := by
      have e1 : (fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * v x)
          = fun x : ℝ => ((deriv (deriv Φ) x : ℝ) : ℂ) * v x
              + (m : ℂ) * (((deriv χ x : ℝ) : ℂ) * v x) := by
        funext x; rw [hdψ x]; push_cast; ring
      have j1 : Integrable (fun x => ((deriv (deriv Φ) x : ℝ) : ℂ) * v x) :=
        integrable_ofReal_mul_of_locallyIntegrable
          (isTestFunction_deriv (isTestFunction_deriv hΦ)) hv
      have j2 : Integrable (fun x => (m : ℂ) * (((deriv χ x : ℝ) : ℂ) * v x)) :=
        (integrable_ofReal_mul_of_locallyIntegrable (isTestFunction_deriv hχ) hv).const_mul _
      rw [e1, integral_add j1 j2, h Φ hΦ, integral_const_mul, ← hk]
      ring
    -- the second integral
    have hB : ∫ x, ((deriv ψ x : ℝ) : ℂ) * (x : ℂ) = -(m : ℂ) := by
      have := integral_deriv_mul (f := fun x : ℝ => ((ψ x : ℝ) : ℂ))
        (f' := fun x : ℝ => ((deriv ψ x : ℝ) : ℂ)) (g := fun x : ℝ => (x : ℂ))
        (g' := fun _ => (1 : ℂ)) (fun x => hψ.hasDerivAt_ofReal x)
        (fun x => by simpa using (Complex.ofRealCLM.hasDerivAt (x := x)))
        hd1.continuous_ofReal continuous_const (hasCompactSupport_ofReal hψ.2)
      rw [this, hm, ← integral_complex_ofReal]
      simp
    rw [hsum, integral_add i1 i2, hA]
    have hBk : ∫ x, ((deriv ψ x : ℝ) : ℂ) * (k * (x : ℂ))
        = k * ∫ x, ((deriv ψ x : ℝ) : ℂ) * (x : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hBk, hB]
    ring
  obtain ⟨c, hcv⟩ := ae_eq_const_of_weak_deriv_eq_zero
    (v := fun x => v x + k * x) (hv.add (by fun_prop : Continuous fun x : ℝ => k * (x : ℂ)
      ).locallyIntegrable) hstep
  refine ⟨c, -k, ?_⟩
  filter_upwards [hcv] with x hx
  have hx' : v x + k * x = c := hx
  linear_combination hx'

/-! ## Continuous versions -/

/-- A continuous function whose distributional derivative vanishes is constant. -/
theorem eq_const_of_weak_deriv_eq_zero {v : ℝ → ℂ} (hv : Continuous v)
    (h : ∀ ψ : ℝ → ℝ, IsTestFunction ψ → ∫ x, ((deriv ψ x : ℝ) : ℂ) * v x = 0) :
    ∃ c : ℂ, ∀ x, v x = c := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_weak_deriv_eq_zero hv.locallyIntegrable h
  exact ⟨c, fun x => congrFun ((hv.ae_eq_iff_eq (μ := volume) continuous_const).mp hc) x⟩

/-- A continuous function whose distributional second derivative vanishes is affine. -/
theorem eq_affine_of_weak_second_deriv_eq_zero {v : ℝ → ℂ} (hv : Continuous v)
    (h : ∀ φ : ℝ → ℝ, IsTestFunction φ → ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * v x = 0) :
    ∃ a b : ℂ, ∀ x, v x = a + b * x := by
  obtain ⟨a, b, hab⟩ := ae_eq_affine_of_weak_second_deriv_eq_zero hv.locallyIntegrable h
  refine ⟨a, b, fun x => congrFun ((hv.ae_eq_iff_eq (μ := volume) (by fun_prop)).mp hab) x⟩

end Brockian.Weyl.DeficiencyODE

import Mathlib

/-!
# Test functions on the line

Basic API for smooth compactly supported functions `ℝ → ℝ`, used to formulate distributional
(weak) solutions of second order ODEs.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace Brockian.Weyl.DeficiencyODE

/-- A test function on `ℝ`: smooth and compactly supported. -/
def IsTestFunction (φ : ℝ → ℝ) : Prop := ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

/-! ## Basic facts about test functions -/

theorem IsTestFunction.contDiff {φ : ℝ → ℝ} (h : IsTestFunction φ) : ContDiff ℝ ∞ φ := h.1

theorem IsTestFunction.hasCompactSupport {φ : ℝ → ℝ} (h : IsTestFunction φ) :
    HasCompactSupport φ := h.2

theorem IsTestFunction.continuous {φ : ℝ → ℝ} (h : IsTestFunction φ) : Continuous φ :=
  h.1.continuous

theorem IsTestFunction.differentiable {φ : ℝ → ℝ} (h : IsTestFunction φ) :
    Differentiable ℝ φ := h.1.differentiable (by simp)

theorem isTestFunction_deriv {φ : ℝ → ℝ} (h : IsTestFunction φ) : IsTestFunction (deriv φ) :=
  ⟨(contDiff_infty_iff_deriv.mp h.1).2, h.2.deriv⟩

theorem IsTestFunction.continuous_ofReal {φ : ℝ → ℝ} (h : IsTestFunction φ) :
    Continuous (fun x => ((φ x : ℝ) : ℂ)) := Complex.continuous_ofReal.comp h.continuous

theorem IsTestFunction.integrable {φ : ℝ → ℝ} (h : IsTestFunction φ) :
    Integrable φ := h.continuous.integrable_of_hasCompactSupport h.2

/-- The complexification of a test function, as a map with a derivative everywhere. -/
theorem IsTestFunction.hasDerivAt_ofReal {φ : ℝ → ℝ} (h : IsTestFunction φ) (x : ℝ) :
    HasDerivAt (fun y => ((φ y : ℝ) : ℂ)) ((deriv φ x : ℝ) : ℂ) x := by
  have := (h.differentiable x).hasDerivAt
  simpa using (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x this)

/-! ## Integrals of compactly supported functions -/

/-- The complexification of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_ofReal {ψ : ℝ → ℝ} (h : HasCompactSupport ψ) :
    HasCompactSupport (fun x => ((ψ x : ℝ) : ℂ)) := by
  refine HasCompactSupport.intro (K := tsupport ψ) h fun x hx => ?_
  simp [image_eq_zero_of_notMem_tsupport hx]

/-- A test function times a continuous function is integrable. -/
theorem integrable_ofReal_mul {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) {w : ℝ → ℂ}
    (hw : Continuous w) : Integrable (fun x => ((ψ x : ℝ) : ℂ) * w x) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_ofReal.comp hψ.continuous).mul hw
  · exact (hasCompactSupport_ofReal hψ.2).mul_right

/-- Rewriting an integral over `ℝ` as an interval integral, when the integrand is supported
inside the interval. -/
theorem integral_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ x, x ∉ Set.Ioc a b → f x = 0) : ∫ x in a..b, f x = ∫ x, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hs

/-- Every compactly supported function with a continuous derivative integrates to zero. -/
theorem integral_deriv_eq_zero {h h' : ℝ → ℂ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (hc : Continuous h') (hcs : HasCompactSupport h) : ∫ x, h' x = 0 := by
  obtain ⟨R, hR⟩ := hcs.isBounded.subset_closedBall (0 : ℝ)
  have hR0 : (0:ℝ) ≤ |R| := abs_nonneg R
  have hab : -(|R| + 1) ≤ |R| + 1 := by linarith
  have hnotmem : ∀ x : ℝ, x ∉ Set.Ioc (-(|R| + 1)) (|R| + 1) → x ∉ tsupport h := by
    intro x hx hmem
    have h1 := hR hmem
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    have h2 : |x| ≤ |R| := le_trans h1 (le_abs_self R)
    have h3 : -|R| ≤ x := neg_le_of_abs_le h2
    have h4 : x ≤ |R| := le_of_abs_le h2
    exact hx ⟨by linarith, by linarith⟩
  have hdh : h' = deriv h := funext fun x => ((hd x).deriv).symm
  have hzero' : ∀ x : ℝ, x ∉ Set.Ioc (-(|R| + 1)) (|R| + 1) → h' x = 0 := by
    intro x hx
    rw [hdh]
    by_contra hne
    exact hnotmem x hx (support_deriv_subset (Function.mem_support.mpr hne))
  have hzeroh : ∀ x : ℝ, |R| < |x| → h x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h1 := hR hmem
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    exact absurd (le_trans h1 (le_abs_self R)) (not_le.mpr hx)
  rw [← integral_eq_intervalIntegral hab hzero']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hc.intervalIntegrable _ _)]
  rw [hzeroh (|R| + 1) (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ |R| + 1)]; linarith),
    hzeroh (-(|R| + 1)) (by
      rw [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ |R| + 1)]; linarith)]
  ring

/-- Integration by parts on the line, for a compactly supported `C¹` factor. -/
theorem integral_deriv_mul {f g f' g' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hf' : Continuous f') (hg' : Continuous g')
    (hcs : HasCompactSupport f) :
    ∫ x, f' x * g x = -∫ x, f x * g' x := by
  have hfc : Continuous f := by
    rw [continuous_iff_continuousAt]; exact fun x => (hf x).continuousAt
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]; exact fun x => (hg x).continuousAt
  have hf'cs : HasCompactSupport f' := by
    have : f' = deriv f := funext fun x => ((hf x).deriv).symm
    rw [this]; exact hcs.deriv
  have hprod : ∀ x, HasDerivAt (fun y => f y * g y) (f' x * g x + f x * g' x) x :=
    fun x => (hf x).mul (hg x)
  have hcs' : HasCompactSupport (fun y => f y * g y) := hcs.mul_right
  have key := integral_deriv_eq_zero hprod (by fun_prop) hcs'
  have h1 : Integrable (fun x => f' x * g x) :=
    (hf'.mul hgc).integrable_of_hasCompactSupport hf'cs.mul_right
  have h2 : Integrable (fun x => f x * g' x) :=
    (hfc.mul hg').integrable_of_hasCompactSupport hcs.mul_right
  rw [integral_add h1 h2] at key
  linear_combination (norm := ring_nf) key

/-! ## A test function of unit mass, and primitives of test functions -/

/-- There is a test function of integral one. -/
theorem exists_testFunction_integral_eq_one :
    ∃ χ : ℝ → ℝ, IsTestFunction χ ∧ ∫ x, χ x = 1 := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨f.normed volume, ⟨f.contDiff_normed (n := ⊤), f.hasCompactSupport_normed⟩, ?_⟩
  exact f.integral_normed

/-- A test function with vanishing integral is the derivative of a test function. -/
theorem IsTestFunction.exists_primitive {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    (h0 : ∫ x, ψ x = 0) : ∃ Φ : ℝ → ℝ, IsTestFunction Φ ∧ _root_.deriv Φ = ψ := by
  obtain ⟨R, hR⟩ := hψ.2.isBounded.subset_closedBall (0 : ℝ)
  set b : ℝ := |R| + 1 with hb
  have hb0 : (0:ℝ) < b := by have := abs_nonneg R; simp only [hb]; linarith
  have hzero : ∀ x : ℝ, b ≤ |x| → ψ x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    have : |x| ≤ |R| := le_trans h1 (le_abs_self R)
    simp only [hb] at hx
    linarith
  set Φ : ℝ → ℝ := fun x => ∫ t in (-b)..x, ψ t with hΦ
  have hderiv : ∀ x, HasDerivAt Φ (ψ x) x := fun x =>
    (hψ.continuous.integral_hasStrictDerivAt (-b) x).hasDerivAt
  have hdΦ : _root_.deriv Φ = ψ := funext fun x => (hderiv x).deriv
  refine ⟨Φ, ⟨?_, ?_⟩, hdΦ⟩
  · refine contDiff_infty_iff_deriv.mpr ⟨fun x => (hderiv x).differentiableAt, ?_⟩
    rw [hdΦ]; exact hψ.1
  · apply HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b))
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · -- `x < -b`
      have : Φ x = ∫ t in (-b)..x, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have : t ≤ -b := by
          rcases le_total x (-b) with h | h
          · rw [Set.uIcc_of_ge h] at ht; exact ht.2
          · linarith
        exact hzero t (by rw [abs_of_nonpos (by linarith)]; linarith)
      simp [this]
    · -- `x > b`
      have hxb : -b ≤ x := by linarith
      have : ∀ y : ℝ, y ∉ Set.Ioc (-b) x → ψ y = 0 := by
        intro y hy
        simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
        rcases hy with hy | hy
        · exact hzero y (by rw [abs_of_nonpos (by linarith)]; linarith)
        · exact hzero y (by rw [abs_of_nonneg (by linarith)]; linarith)
      have h2 : (∫ t in (-b)..x, ψ t) = ∫ t, ψ t := by
        rw [intervalIntegral.integral_of_le hxb]
        exact setIntegral_eq_integral_of_forall_compl_eq_zero this
      rw [hΦ]
      simpa [h2] using h0

/-! ## Locally integrable functions -/

/-- A locally integrable function on `ℝ` is interval integrable on every interval. -/
theorem locallyIntegrable_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    {g : ℝ → E} (hg : LocallyIntegrable g volume) (a b : ℝ) :
    IntervalIntegrable g volume a b :=
  intervalIntegrable_iff.mpr
    ((hg.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc)

/-- A test function times a locally integrable function is integrable. -/
theorem integrable_ofReal_mul_of_locallyIntegrable {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    {w : ℝ → ℂ} (hw : LocallyIntegrable w volume) :
    Integrable (fun x => ((ψ x : ℝ) : ℂ) * w x) := by
  have hli : LocallyIntegrable (fun x => ((ψ x : ℝ) : ℂ) * w x) volume := by
    rw [← locallyIntegrableOn_univ] at hw ⊢
    exact hw.continuousOn_mul hψ.continuous_ofReal.continuousOn
      (IsClosed.isLocallyClosed isClosed_univ)
  have hcs : HasCompactSupport (fun x => ((ψ x : ℝ) : ℂ) * w x) :=
    (hasCompactSupport_ofReal hψ.2).mul_right
  refine (hli.integrableOn_isCompact hcs.isCompact).integrable_of_forall_notMem_eq_zero ?_
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (f := fun y => ((ψ y : ℝ) : ℂ) * w y) hx

/-- A test function is globally Lipschitz. -/
theorem IsTestFunction.exists_lipschitzWith {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) :
    ∃ K : NNReal, LipschitzWith K ψ := by
  obtain ⟨C, hC⟩ := (continuous_norm.comp (isTestFunction_deriv hψ).continuous
    ).bounded_above_of_compact_support hψ.2.deriv.norm
  have hC' : ∀ x, ‖deriv ψ x‖ ≤ C := fun x => by simpa using hC x
  have hC0 : (0:ℝ) ≤ C := le_trans (norm_nonneg _) (hC' 0)
  refine ⟨C.toNNReal, lipschitzWith_of_nnnorm_deriv_le hψ.differentiable fun x => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC0]
  exact hC' x

/-! ## Integration by parts against the primitive of a locally integrable function -/

/-- **Integration by parts** against the primitive of a locally integrable real function:
if `ψ` is a test function and `g` is locally integrable, then
`∫ ψ' (x) (∫_0^x g) dx = -∫ ψ g`. -/
theorem integral_deriv_mul_primitive_real {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    {g : ℝ → ℝ} (hg : LocallyIntegrable g volume) :
    ∫ x, deriv ψ x * (∫ t in (0:ℝ)..x, g t) = -∫ x, ψ x * g x := by
  set H : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, g t with hH
  obtain ⟨R, hR⟩ := hψ.2.isBounded.subset_closedBall (0 : ℝ)
  have hR0 : (0:ℝ) ≤ |R| := abs_nonneg R
  have hR1 : (0:ℝ) ≤ |R| + 1 := by linarith
  set A : ℝ := -(|R| + 1) with hA
  set B : ℝ := |R| + 1 with hB
  have hAB : A ≤ B := by simp only [hA, hB]; linarith
  have habs : ∀ x : ℝ, x ∈ tsupport ψ → |x| ≤ |R| := by
    intro x hmem
    have h1 := hR hmem
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
    exact le_trans h1 (le_abs_self R)
  have hmemtsupp : ∀ x : ℝ, x ∈ tsupport ψ → x ∈ Set.Ioc A B := by
    intro x hmem
    have h2 := habs x hmem
    exact ⟨by simp only [hA]; have := neg_le_of_abs_le h2; linarith,
      by simp only [hB]; have := le_of_abs_le h2; linarith⟩
  have hvanψ : ∀ x : ℝ, x ∉ Set.Ioc A B → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hmem => hx (hmemtsupp x hmem))
  have hvandψ : ∀ x : ℝ, x ∉ Set.Ioc A B → deriv ψ x = 0 := by
    intro x hx
    by_contra hne
    exact hx (hmemtsupp x (support_deriv_subset (Function.mem_support.mpr hne)))
  have hvanAbs : ∀ x : ℝ, |R| < |x| → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hmem => absurd (habs x hmem) (not_le.mpr hx))
  have hψA : ψ A = 0 := hvanAbs A (by rw [hA, abs_neg, abs_of_nonneg hR1, hB]; linarith)
  have hψB : ψ B = 0 := hvanAbs B (by rw [abs_of_nonneg hR1, hB]; linarith)
  have h0mem : (0:ℝ) ∈ Set.uIcc A B := by
    rw [Set.uIcc_of_le hAB]
    constructor <;> [simp only [hA]; simp only [hB]] <;> linarith
  have hACH : AbsolutelyContinuousOnInterval H A B :=
    (locallyIntegrable_intervalIntegrable hg A B).absolutelyContinuousOnInterval_intervalIntegral
      h0mem
  have hACψ : AbsolutelyContinuousOnInterval ψ A B := by
    obtain ⟨K, hK⟩ := hψ.exists_lipschitzWith
    exact LipschitzOnWith.absolutelyContinuousOnInterval (K := K) hK.lipschitzOnWith
  have IBP := hACψ.integral_mul_deriv_eq_deriv_mul hACH
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc A B → ψ x * deriv H x = ψ x * g x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg] with x hx _
    rw [(hx 0).deriv]
  rw [intervalIntegral.integral_congr_ae hae, hψA, hψB] at IBP
  have e1 : ∫ x, ψ x * g x = ∫ x in A..B, ψ x * g x :=
    (integral_eq_intervalIntegral hAB (fun x hx => by rw [hvanψ x hx]; ring)).symm
  have e2 : ∫ x, deriv ψ x * H x = ∫ x in A..B, deriv ψ x * H x :=
    (integral_eq_intervalIntegral hAB (fun x hx => by rw [hvandψ x hx]; ring)).symm
  rw [e1, e2]
  linarith [IBP]

/-- **Integration by parts** against the primitive of a locally integrable complex function. -/
theorem integral_deriv_mul_primitive {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    {g : ℝ → ℂ} (hg : LocallyIntegrable g volume) :
    ∫ x, ((deriv ψ x : ℝ) : ℂ) * (∫ t in (0:ℝ)..x, g t) = -∫ x, ((ψ x : ℝ) : ℂ) * g x := by
  set H : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, g t with hH
  have hHc : Continuous H :=
    intervalIntegral.continuous_primitive (locallyIntegrable_intervalIntegrable hg) 0
  have hint1 : Integrable (fun x => ((deriv ψ x : ℝ) : ℂ) * H x) volume :=
    integrable_ofReal_mul (isTestFunction_deriv hψ) hHc
  have hint2 : Integrable (fun x => ((ψ x : ℝ) : ℂ) * g x) volume :=
    integrable_ofReal_mul_of_locallyIntegrable hψ hg
  -- it suffices to compare the images under the real-linear maps `re` and `im`
  have key : ∀ L : ℂ →L[ℝ] ℝ, (∀ (r : ℝ) (w : ℂ), L ((r : ℂ) * w) = r * L w) →
      L (∫ x, ((deriv ψ x : ℝ) : ℂ) * H x) = L (-∫ x, ((ψ x : ℝ) : ℂ) * g x) := by
    intro L hL
    have hLg : LocallyIntegrable (fun x => L (g x)) volume := by
      intro x
      obtain ⟨s, hs, hint⟩ := hg x
      exact ⟨s, hs, (L.integrable_comp hint)⟩
    have hLH : ∀ x, L (H x) = ∫ t in (0:ℝ)..x, L (g t) := fun x =>
      (L.intervalIntegral_comp_comm (locallyIntegrable_intervalIntegrable hg 0 x)).symm
    have p1 : ∀ x : ℝ, L (((deriv ψ x : ℝ) : ℂ) * H x)
        = deriv ψ x * (∫ t in (0:ℝ)..x, L (g t)) := fun x => by rw [hL, hLH]
    have p2 : ∀ x : ℝ, L (((ψ x : ℝ) : ℂ) * g x) = ψ x * L (g x) := fun x => by rw [hL]
    have e1 : L (∫ x, ((deriv ψ x : ℝ) : ℂ) * H x)
        = ∫ x, deriv ψ x * (∫ t in (0:ℝ)..x, L (g t)) := by
      rw [← L.integral_comp_comm hint1]
      exact integral_congr_ae (Filter.Eventually.of_forall p1)
    have e2 : L (∫ x, ((ψ x : ℝ) : ℂ) * g x) = ∫ x, ψ x * L (g x) := by
      rw [← L.integral_comp_comm hint2]
      exact integral_congr_ae (Filter.Eventually.of_forall p2)
    rw [e1, map_neg, e2, integral_deriv_mul_primitive_real hψ hLg]
  refine Complex.ext ?_ ?_
  · simpa using key Complex.reCLM (fun r w => by simp)
  · simpa using key Complex.imCLM (fun r w => by simp)

end Brockian.Weyl.DeficiencyODE

import Brockian.Weyl.DuBoisReymond

/-!
# Deficiency elements of a Sturm–Liouville expression solve the ODE

This file contains the elliptic-regularity ("deficiency represents ODE") statement in one
dimension: any *distributional* solution of the Weyl deficiency equation

`u'' = (q - z) u`

is, after modification on a null set, a classical `C²` solution.  No regularity whatsoever is
assumed on `u` beyond local integrability (which is needed for the distributional formulation
to make sense at all); in particular, the deficiency elements of the minimal operator, which
are a priori only `L²` functions, are genuine solutions of the ordinary differential equation.
-/

open MeasureTheory Filter
open scoped Topology ContDiff NNReal

namespace Brockian.Weyl.DeficiencyODE

/-- `u` is a distributional (weak) solution of the deficiency equation `u'' = (q - z) u`. -/
def IsWeakDeficiencySolution (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ∀ φ : ℝ → ℝ, IsTestFunction φ →
    ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * u x = ∫ x, ((φ x : ℝ) : ℂ) * ((q x - z) * u x)

/-- `u` is a classical solution of the deficiency equation `u'' = (q - z) u`. -/
def IsClassicalDeficiencySolution (q : ℝ → ℂ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 u ∧ ∀ x, deriv (deriv u) x = (q x - z) * u x

/-! ## Main theorem -/

/-- **Deficiency elements solve the ODE.**  A locally integrable distributional solution of the
Weyl deficiency equation `u'' = (q - z) u`, with continuous potential `q`, agrees almost
everywhere with a classical `C²` solution of the same equation.

No regularity hypothesis is imposed on `u`: local integrability is exactly what is needed for
the weak formulation to be meaningful. -/
theorem deficiencyRepresentsODE_of_weakRegularity {q : ℝ → ℂ} {z : ℂ} {u : ℝ → ℂ}
    (hq : Continuous q) (hu : LocallyIntegrable u volume) (hw : IsWeakDeficiencySolution q z u) :
    ∃ w : ℝ → ℂ, IsClassicalDeficiencySolution q z w ∧ u =ᵐ[volume] w := by
  set g : ℝ → ℂ := fun x => (q x - z) * u x with hg
  have hgl : LocallyIntegrable g volume := by
    rw [← locallyIntegrableOn_univ] at hu ⊢
    exact hu.continuousOn_mul (hq.sub continuous_const).continuousOn
      (IsClosed.isLocallyClosed isClosed_univ)
  -- the first primitive of `g`
  set G₁ : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, g t with hG₁
  have hG₁c : Continuous G₁ :=
    intervalIntegral.continuous_primitive (locallyIntegrable_intervalIntegrable hgl) 0
  -- the second primitive of `g`
  set W : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, G₁ t with hW
  have hWd : ∀ x, HasDerivAt W (G₁ x) x := fun x =>
    (hG₁c.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hWc : Continuous W := by
    rw [continuous_iff_continuousAt]; exact fun x => (hWd x).continuousAt
  -- `W` is a distributional solution of the inhomogeneous equation `W'' = g`
  have hIBP : ∀ φ : ℝ → ℝ, IsTestFunction φ →
      ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * W x = ∫ x, ((φ x : ℝ) : ℂ) * g x := by
    intro φ hφ
    have h1 : ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * W x = -∫ x, ((deriv φ x : ℝ) : ℂ) * G₁ x :=
      integral_deriv_mul (fun x => (isTestFunction_deriv hφ).hasDerivAt_ofReal x) hWd
        (isTestFunction_deriv (isTestFunction_deriv hφ)).continuous_ofReal hG₁c
        (hasCompactSupport_ofReal (isTestFunction_deriv hφ).2)
    have h2 : ∫ x, ((deriv φ x : ℝ) : ℂ) * G₁ x = -∫ x, ((φ x : ℝ) : ℂ) * g x :=
      integral_deriv_mul_primitive hφ hgl
    rw [h1, h2]; ring
  -- hence `u - W` has vanishing distributional second derivative
  have hvan : ∀ φ : ℝ → ℝ, IsTestFunction φ →
      ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * (u x - W x) = 0 := by
    intro φ hφ
    have hd2 : IsTestFunction (deriv (deriv φ)) :=
      isTestFunction_deriv (isTestFunction_deriv hφ)
    have i1 : Integrable (fun x => ((deriv (deriv φ) x : ℝ) : ℂ) * u x) :=
      integrable_ofReal_mul_of_locallyIntegrable hd2 hu
    have i2 : Integrable (fun x => ((deriv (deriv φ) x : ℝ) : ℂ) * W x) :=
      integrable_ofReal_mul hd2 hWc
    have e : (fun x : ℝ => ((deriv (deriv φ) x : ℝ) : ℂ) * (u x - W x))
        = fun x : ℝ => ((deriv (deriv φ) x : ℝ) : ℂ) * u x
            - ((deriv (deriv φ) x : ℝ) : ℂ) * W x := by
      funext x; ring
    rw [e, integral_sub i1 i2, hw φ hφ, hIBP φ hφ, hg]
    simp
  obtain ⟨a, b, hab⟩ := ae_eq_affine_of_weak_second_deriv_eq_zero
    (hu.sub hWc.locallyIntegrable) hvan
  -- the classical solution
  set w : ℝ → ℂ := fun x => W x + (a + b * x) with hwdef
  have huw : u =ᵐ[volume] w := by
    filter_upwards [hab] with x hx
    have hx' : u x - W x = a + b * x := hx
    simp only [hwdef]
    linear_combination hx'
  -- bootstrap: `g` agrees a.e. with the continuous function `(q - z) * w`
  have hgw : g =ᵐ[volume] fun x => (q x - z) * w x := by
    filter_upwards [huw] with x hx
    simp only [hg, hx]
  have hgwc : Continuous (fun x => (q x - z) * w x) :=
    (hq.sub continuous_const).mul (hWc.add (by fun_prop))
  have hG₁eq : G₁ = fun x => ∫ t in (0:ℝ)..x, (q t - z) * w t := by
    funext x
    exact intervalIntegral.integral_congr_ae (by filter_upwards [hgw] with t ht _ using ht)
  have hG₁d : ∀ x, HasDerivAt G₁ ((q x - z) * w x) x := by
    intro x
    rw [hG₁eq]
    exact (hgwc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hwd : ∀ x, HasDerivAt w (G₁ x + b) x := by
    intro x
    have hlin : HasDerivAt (fun y : ℝ => a + b * (y : ℂ)) b x := by
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x))
      simpa using ((h1.const_mul b).const_add a)
    exact (hWd x).add hlin
  have hdw : deriv w = fun x => G₁ x + b := funext fun x => (hwd x).deriv
  have hdw2 : ∀ x, HasDerivAt (deriv w) ((q x - z) * w x) x := by
    rw [hdw]; intro x; simpa using (hG₁d x).add_const b
  have hddw : deriv (deriv w) = fun x => (q x - z) * w x := funext fun x => (hdw2 x).deriv
  refine ⟨w, ⟨?_, fun x => by rw [hddw]⟩, huw⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hwd x).differentiableAt, by simp, ?_⟩
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x => (hdw2 x).differentiableAt, by rw [hddw]; exact hgwc⟩

/-- **Continuous deficiency elements are classical solutions.**  A continuous distributional
solution of `u'' = (q - z) u` with continuous potential `q` is itself a classical `C²`
solution. -/
theorem deficiencyRepresentsODE_of_continuous {q : ℝ → ℂ} {z : ℂ} {u : ℝ → ℂ}
    (hq : Continuous q) (hu : Continuous u) (hw : IsWeakDeficiencySolution q z u) :
    IsClassicalDeficiencySolution q z u := by
  obtain ⟨w, ⟨hw2, hwode⟩, huw⟩ :=
    deficiencyRepresentsODE_of_weakRegularity hq hu.locallyIntegrable hw
  have hwc : Continuous w := hw2.continuous
  have : u = w := (hu.ae_eq_iff_eq (μ := volume) hwc).mp huw
  rw [this]
  exact ⟨hw2, hwode⟩

/-- Sanity check (converse direction): a classical solution is a distributional solution. -/
theorem IsClassicalDeficiencySolution.isWeakDeficiencySolution {q : ℝ → ℂ} {z : ℂ} {u : ℝ → ℂ}
    (h : IsClassicalDeficiencySolution q z u) : IsWeakDeficiencySolution q z u := by
  obtain ⟨hu2, hode⟩ := h
  obtain ⟨hdiff, -, hC1⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) u from hu2)
  have hu1 : ∀ x, HasDerivAt u (deriv u x) x := fun x => (hdiff x).hasDerivAt
  have hu1' : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x =>
    ((contDiff_one_iff_deriv.mp hC1).1 x).hasDerivAt
  have hcu1 : Continuous (deriv u) := hC1.continuous
  have hcu2 : Continuous (deriv (deriv u)) := (contDiff_one_iff_deriv.mp hC1).2
  intro φ hφ
  have h1 : ∫ x, ((deriv (deriv φ) x : ℝ) : ℂ) * u x = -∫ x, ((deriv φ x : ℝ) : ℂ) * deriv u x :=
    integral_deriv_mul (fun x => (isTestFunction_deriv hφ).hasDerivAt_ofReal x) hu1
      (isTestFunction_deriv (isTestFunction_deriv hφ)).continuous_ofReal hcu1
      (hasCompactSupport_ofReal (isTestFunction_deriv hφ).2)
  have h2 : ∫ x, ((deriv φ x : ℝ) : ℂ) * deriv u x
      = -∫ x, ((φ x : ℝ) : ℂ) * deriv (deriv u) x :=
    integral_deriv_mul (fun x => hφ.hasDerivAt_ofReal x) hu1'
      (isTestFunction_deriv hφ).continuous_ofReal hcu2 (hasCompactSupport_ofReal hφ.2)
  rw [h1, h2, neg_neg]
  have hpt : ∀ x : ℝ, ((φ x : ℝ) : ℂ) * deriv (deriv u) x
      = ((φ x : ℝ) : ℂ) * ((q x - z) * u x) := fun x => by rw [hode x]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end Brockian.Weyl.DeficiencyODE

