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

import Brockian.Weyl.WeakDerivative

/-!
# Weyl deficiency spaces are represented by solutions of the Schrödinger ODE

For a continuous potential `q : ℝ → ℝ` and a spectral parameter `z : ℂ`, consider the
formally symmetric differential expression `τ u = -u'' + q u` on the line.  The minimal
operator is the restriction of `τ` to test functions, and the deficiency space at `z`
consists of the `L²` functions `u` which satisfy `τ u = z u` *weakly*, i.e. in the sense
of distributions:

  `∫ u φ'' = ∫ (q - z) u φ`   for all real test functions `φ`.

The main result of this file, `deficiencyRepresentsODE_of_weakRegularity`, states that
this deficiency space coincides with the set of `L²` functions which agree almost
everywhere with a *classical* (twice differentiable) solution of the ODE
`-u'' + q u = z u`.

The nontrivial inclusion is a regularity statement — every weak solution is almost
everywhere a classical solution — which is proved here from scratch (`weakRegularity`)
from the du Bois-Reymond lemmas of `Brockian.Weyl.WeakDerivative`; consequently the final
theorem carries no regularity hypothesis.
-/

open MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

open Brockian.Weyl

/-- `u` solves `-u'' + q u = z u` in the sense of distributions. -/
def WeakSolution (q : ℝ → ℝ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ∀ φ : ℝ → ℝ, IsTestFunction φ →
    ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * u x = ∫ x : ℝ, (φ x : ℂ) * ((q x - z) * u x)

/-- `u` solves `-u'' + q u = z u` classically: `u` is differentiable with derivative `u'`,
and `u'` is differentiable with derivative `(q - z) u`. -/
def ClassicalSolution (q : ℝ → ℝ) (z : ℂ) (u : ℝ → ℂ) : Prop :=
  ∃ u' : ℝ → ℂ, (∀ x, HasDerivAt u (u' x) x) ∧ ∀ x, HasDerivAt u' ((q x - z) * u x) x

/-- The deficiency space at `z`: the `L²` distributional solutions of `τ u = z u`. -/
def deficiencySet (q : ℝ → ℝ) (z : ℂ) : Set (ℝ → ℂ) :=
  {u | MemLp u 2 volume ∧ WeakSolution q z u}

/-- The set of `L²` functions agreeing a.e. with a classical solution of
`-u'' + q u = z u`. -/
def odeSolutionSet (q : ℝ → ℝ) (z : ℂ) : Set (ℝ → ℂ) :=
  {u | MemLp u 2 volume ∧ ∃ v : ℝ → ℂ, ClassicalSolution q z v ∧ u =ᵐ[volume] v}

/-- A classical solution is continuous. -/
theorem ClassicalSolution.continuous {q : ℝ → ℝ} {z : ℂ} {u : ℝ → ℂ}
    (h : ClassicalSolution q z u) : Continuous u :=
  continuous_iff_continuousAt.mpr fun x => (h.choose_spec.1 x).continuousAt

/-- Being a weak solution only depends on the a.e. equivalence class. -/
theorem WeakSolution.congr_ae {q : ℝ → ℝ} {z : ℂ} {u v : ℝ → ℂ} (hae : u =ᵐ[volume] v)
    (h : WeakSolution q z u) : WeakSolution q z v := by
  intro φ hφ
  have h1 : ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * v x
      = ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * u x := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  have h2 : ∫ x : ℝ, (φ x : ℂ) * ((q x - z) * v x)
      = ∫ x : ℝ, (φ x : ℂ) * ((q x - z) * u x) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  rw [h1, h2, h φ hφ]

/-- A classical solution is a weak solution. -/
theorem WeakSolution.of_classical {q : ℝ → ℝ} (hq : Continuous q) {z : ℂ} {u : ℝ → ℂ}
    (h : ClassicalSolution q z u) : WeakSolution q z u := by
  obtain ⟨u', hu', hu''⟩ := h
  have huc : Continuous u := continuous_iff_continuousAt.mpr fun x => (hu' x).continuousAt
  have hu'c : Continuous u' := continuous_iff_continuousAt.mpr fun x => (hu'' x).continuousAt
  have hgc : Continuous (fun x => ((q x : ℂ) - z) * u x) :=
    ((Complex.continuous_ofReal.comp hq).sub continuous_const).mul huc
  intro φ hφ
  rw [integral_deriv_testFunction_mul hu' hu'c hφ.deriv',
    integral_deriv_testFunction_mul hu'' hgc hφ, neg_neg]

/-- A sanity check that the notions above are not vacuous: for `q = 0` and `z = 1` the
function `x ↦ exp (i x)` is a classical solution of `-u'' + q u = z u`. -/
theorem classicalSolution_exp_I :
    ClassicalSolution (fun _ => 0) 1 (fun x : ℝ => Complex.exp (Complex.I * x)) := by
  refine ⟨fun x => Complex.I * Complex.exp (Complex.I * x), fun x => ?_, fun x => ?_⟩
  · have h := (((hasDerivAt_id x).ofReal_comp).const_mul Complex.I).cexp
    simpa [mul_comm] using h
  · have h := ((((hasDerivAt_id x).ofReal_comp).const_mul Complex.I).cexp).const_mul Complex.I
    simp only [id, Complex.ofReal_one, mul_one] at h
    convert h using 1
    simp only [Complex.ofReal_zero, zero_sub]
    ring_nf
    rw [Complex.I_sq]
    ring

/-- The corresponding weak solution, obtained from `WeakSolution.of_classical`. -/
theorem weakSolution_exp_I :
    WeakSolution (fun _ => 0) 1 (fun x : ℝ => Complex.exp (Complex.I * x)) :=
  WeakSolution.of_classical continuous_const classicalSolution_exp_I

/-! ### Weak regularity -/

/-- Every continuous distributional solution of `-u'' + q u = z u` is a classical
solution. -/
theorem classicalSolution_of_continuous_weakSolution {q : ℝ → ℝ} (hq : Continuous q) {z : ℂ}
    {u : ℝ → ℂ} (hu : Continuous u) (hweak : WeakSolution q z u) : ClassicalSolution q z u := by
  set g : ℝ → ℂ := fun x => ((q x : ℂ) - z) * u x with hg
  have hgc : Continuous g := ((Complex.continuous_ofReal.comp hq).sub continuous_const).mul hu
  set G₁ : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, g t with hG₁
  have hG₁d : ∀ x, HasDerivAt G₁ (g x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  have hG₁c : Continuous G₁ := continuous_iff_continuousAt.mpr fun x => (hG₁d x).continuousAt
  set G₂ : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, G₁ t with hG₂
  have hG₂d : ∀ x, HasDerivAt G₂ (G₁ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hG₁c.intervalIntegrable _ _)
      (hG₁c.stronglyMeasurableAtFilter _ _) hG₁c.continuousAt
  have hG₂c : Continuous G₂ := continuous_iff_continuousAt.mpr fun x => (hG₂d x).continuousAt
  have hG₂weak : ∀ φ : ℝ → ℝ, IsTestFunction φ →
      ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * G₂ x = ∫ x : ℝ, (φ x : ℂ) * g x := by
    intro φ hφ
    rw [integral_deriv_testFunction_mul hG₂d hG₁c hφ.deriv',
      integral_deriv_testFunction_mul hG₁d hgc hφ, neg_neg]
  have hdiff : ∀ φ : ℝ → ℝ, IsTestFunction φ →
      ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * (u x - G₂ x) = 0 := by
    intro φ hφ
    have hsplit : ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * (u x - G₂ x)
        = (∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * u x)
          - ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * G₂ x := by
      rw [← integral_sub (hφ.deriv'.deriv'.integrable_mul hu.locallyIntegrable)
        (hφ.deriv'.deriv'.integrable_mul hG₂c.locallyIntegrable)]
      congr 1
      ext x
      ring
    rw [hsplit, hweak φ hφ, hG₂weak φ hφ, sub_self]
  obtain ⟨c₀, c₁, hc⟩ := ae_affine_of_weak_second_deriv_eq_zero
    (hu.sub hG₂c).locallyIntegrable hdiff
  have hueq : u = fun x => G₂ x + (c₀ + c₁ * x) := by
    have hcont : Continuous fun x : ℝ => G₂ x + (c₀ + c₁ * (x : ℂ)) := by fun_prop
    have hae : u =ᵐ[volume] fun x => G₂ x + (c₀ + c₁ * x) := by
      filter_upwards [hc] with x hx
      have hx' : u x - G₂ x = c₀ + c₁ * x := hx
      linear_combination hx'
    exact (Continuous.ae_eq_iff_eq volume hu hcont).mp hae
  refine ⟨fun x => G₁ x + c₁, fun x => ?_, fun x => ?_⟩
  · rw [hueq]
    have hlin : HasDerivAt (fun x : ℝ => c₀ + c₁ * x) c₁ x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul c₁ |>.const_add c₀
    exact (hG₂d x).add hlin
  · exact (hG₁d x).add_const c₁

/-- Every locally integrable distributional solution of `-u'' + q u = z u` agrees almost
everywhere with a continuous function. -/
theorem exists_continuous_ae_eq_of_weakSolution {q : ℝ → ℝ} (hq : Continuous q) {z : ℂ}
    {u : ℝ → ℂ} (hu : LocallyIntegrable u volume) (hweak : WeakSolution q z u) :
    ∃ v : ℝ → ℂ, Continuous v ∧ u =ᵐ[volume] v := by
  set g : ℝ → ℂ := fun x => ((q x : ℂ) - z) * u x with hg
  have hgl : LocallyIntegrable g volume := by
    rw [← locallyIntegrableOn_univ] at hu ⊢
    exact hu.continuousOn_mul
      (((Complex.continuous_ofReal.comp hq).sub continuous_const).continuousOn)
      isClosed_univ.isLocallyClosed
  set G₁ : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, g t with hG₁
  have hG₁c : Continuous G₁ :=
    intervalIntegral.continuous_primitive
      (fun a b => (hgl.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) 0
  set G₂ : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, G₁ t with hG₂
  have hG₂d : ∀ x, HasDerivAt G₂ (G₁ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hG₁c.intervalIntegrable _ _)
      (hG₁c.stronglyMeasurableAtFilter _ _) hG₁c.continuousAt
  have hG₂c : Continuous G₂ := continuous_iff_continuousAt.mpr fun x => (hG₂d x).continuousAt
  have hG₂weak : ∀ φ : ℝ → ℝ, IsTestFunction φ →
      ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * G₂ x = ∫ x : ℝ, (φ x : ℂ) * g x := by
    intro φ hφ
    rw [integral_deriv_testFunction_mul hG₂d hG₁c hφ.deriv',
      integral_deriv_testFunction_mul_primitive hφ hgl, neg_neg]
  have hdiff : ∀ φ : ℝ → ℝ, IsTestFunction φ →
      ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * (u x - G₂ x) = 0 := by
    intro φ hφ
    have hsplit : ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * (u x - G₂ x)
        = (∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * u x)
          - ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * G₂ x := by
      rw [← integral_sub (hφ.deriv'.deriv'.integrable_mul hu)
        (hφ.deriv'.deriv'.integrable_mul hG₂c.locallyIntegrable)]
      congr 1
      ext x
      ring
    rw [hsplit, hweak φ hφ, hG₂weak φ hφ, sub_self]
  obtain ⟨c₀, c₁, hc⟩ := ae_affine_of_weak_second_deriv_eq_zero
    (hu.sub hG₂c.locallyIntegrable) hdiff
  refine ⟨fun x => G₂ x + (c₀ + c₁ * x), by fun_prop, ?_⟩
  filter_upwards [hc] with x hx
  have hx' : u x - G₂ x = c₀ + c₁ * x := hx
  linear_combination hx'

/-- **Weak regularity**: every locally integrable distributional solution of
`-u'' + q u = z u` agrees almost everywhere with a classical solution.  This is the
hypothesis that the main theorem used to assume. -/
theorem weakRegularity {q : ℝ → ℝ} (hq : Continuous q) {z : ℂ} {u : ℝ → ℂ}
    (hu : LocallyIntegrable u volume) (hweak : WeakSolution q z u) :
    ∃ v : ℝ → ℂ, ClassicalSolution q z v ∧ u =ᵐ[volume] v := by
  obtain ⟨v, hvc, hae⟩ := exists_continuous_ae_eq_of_weakSolution hq hu hweak
  exact ⟨v, classicalSolution_of_continuous_weakSolution hq hvc (hweak.congr_ae hae), hae⟩

/-- **The deficiency space is represented by the ODE.**  For a continuous potential `q`
and any `z : ℂ`, the deficiency space at `z` — the `L²` distributional solutions of
`-u'' + q u = z u` — consists exactly of the `L²` functions that agree almost everywhere
with a classical solution of that ODE.  The regularity hypothesis is discharged by
`weakRegularity`, so the statement is unconditional. -/
theorem deficiencyRepresentsODE_of_weakRegularity {q : ℝ → ℝ} (hq : Continuous q) (z : ℂ) :
    deficiencySet q z = odeSolutionSet q z := by
  ext u
  constructor
  · rintro ⟨hL2, hweak⟩
    exact ⟨hL2, weakRegularity hq (hL2.locallyIntegrable one_le_two) hweak⟩
  · rintro ⟨hL2, v, hv, hae⟩
    exact ⟨hL2, (WeakSolution.of_classical hq hv).congr_ae hae.symm⟩

end Brockian.Weyl.DeficiencyODE

import Mathlib

/-!
# Test functions and weak derivatives on the line

This file develops the small amount of one-dimensional distribution theory needed for the
regularity theory of Sturm–Liouville operators:

* `Brockian.Weyl.IsTestFunction`: smooth, compactly supported real functions on `ℝ`;
* integration by parts against a test function
  (`Brockian.Weyl.integral_deriv_testFunction_mul` for everywhere differentiable functions,
  `Brockian.Weyl.integral_deriv_testFunction_mul_primitive` for primitives of locally
  integrable functions);
* the du Bois-Reymond lemmas `Brockian.Weyl.ae_const_of_weak_deriv_eq_zero` and
  `Brockian.Weyl.ae_affine_of_weak_second_deriv_eq_zero`, saying that a locally integrable
  function whose first (resp. second) distributional derivative vanishes is almost
  everywhere constant (resp. affine).
-/

open MeasureTheory

namespace Brockian.Weyl

/-- A (real valued) test function on the line: smooth with compact support. -/
def IsTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ

namespace IsTestFunction

theorem continuous {φ : ℝ → ℝ} (hφ : IsTestFunction φ) : Continuous φ := hφ.1.continuous

theorem contDiff_one {φ : ℝ → ℝ} (hφ : IsTestFunction φ) : ContDiff ℝ 1 φ :=
  hφ.1.of_le (by exact_mod_cast le_top)

theorem differentiable {φ : ℝ → ℝ} (hφ : IsTestFunction φ) : Differentiable ℝ φ :=
  (contDiff_infty_iff_deriv.mp hφ.1).1

theorem deriv' {φ : ℝ → ℝ} (hφ : IsTestFunction φ) : IsTestFunction (deriv φ) :=
  ⟨(contDiff_infty_iff_deriv.mp hφ.1).2, hφ.2.deriv⟩

theorem integrable {φ : ℝ → ℝ} (hφ : IsTestFunction φ) : Integrable φ volume :=
  hφ.continuous.integrable_of_hasCompactSupport hφ.2

/-- A test function times a locally integrable function is integrable. -/
theorem integrable_mul {φ : ℝ → ℝ} (hφ : IsTestFunction φ) {v : ℝ → ℂ}
    (hv : LocallyIntegrable v volume) : Integrable (fun x => (φ x : ℂ) * v x) volume := by
  obtain ⟨C, hC⟩ := hφ.2.exists_bound_of_continuous hφ.continuous
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport φ) ?_ ?_
  · exact Integrable.bdd_mul (c := C) (hv.integrableOn_isCompact hφ.2)
      (Complex.continuous_ofReal.comp hφ.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  · intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]

/-- The integral of the derivative of a test function vanishes. -/
theorem integral_deriv_eq_zero {φ : ℝ → ℝ} (hφ : IsTestFunction φ) :
    ∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) = 0 := by
  rw [integral_complex_ofReal]
  norm_cast
  exact MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hφ.differentiable x).hasDerivAt) hφ.deriv'.integrable hφ.integrable

end IsTestFunction

/-- There is a test function of total integral one. -/
theorem exists_testFunction_integral_one :
    ∃ ρ : ℝ → ℝ, IsTestFunction ρ ∧ ∫ x : ℝ, ρ x = 1 := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩
  exact ⟨f.normed volume, ⟨f.contDiff_normed, f.hasCompactSupport_normed⟩, f.integral_normed⟩

/-- A test function with vanishing integral is the derivative of a test function. -/
theorem exists_testFunction_hasDerivAt {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ)
    (h0 : ∫ x : ℝ, ψ x = 0) :
    ∃ θ : ℝ → ℝ, IsTestFunction θ ∧ ∀ x, HasDerivAt θ (ψ x) x := by
  obtain ⟨R, hR0, hR⟩ := hψ.2.exists_pos_le_norm
  have hcont : Continuous ψ := hψ.continuous
  refine ⟨fun x => ∫ t in (-R)..x, ψ t, ⟨?_, ?_⟩, ?_⟩
  · refine contDiff_infty_iff_deriv.mpr ⟨fun x => ?_, ?_⟩
    · exact (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
        (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).differentiableAt
    · have hdeq : (deriv fun x => ∫ t in (-R)..x, ψ t) = ψ := funext fun x =>
        (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
          (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).deriv
      rw [hdeq]; exact hψ.1
  · refine HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc ?_
    intro x hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · have hzero : Set.EqOn ψ (fun _ => (0 : ℝ)) (Set.uIcc (-R) x) := by
        intro t ht
        rw [Set.uIcc_comm, Set.uIcc_of_le h.le] at ht
        exact hR t (by
          rw [Real.norm_eq_abs, abs_of_nonpos (le_trans ht.2 (by linarith))]
          linarith [ht.2])
      rw [intervalIntegral.integral_congr hzero]
      simp
    · rw [intervalIntegral.integral_eq_integral_of_support_subset (a := -R) (b := x), h0]
      intro t ht
      have habs : |t| < R := by
        by_contra hc
        exact ht (hR t (by rw [Real.norm_eq_abs]; linarith [not_lt.mp hc]))
      rw [abs_lt] at habs
      exact ⟨habs.1, le_of_lt (lt_trans habs.2 h)⟩
  · exact fun x => intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

/-- Integration by parts against a test function, for an everywhere differentiable
function with continuous derivative. -/
theorem integral_deriv_testFunction_mul {F f : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hf : Continuous f) {ψ : ℝ → ℝ} (hψ : IsTestFunction ψ) :
    ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * F x = -∫ x : ℝ, (ψ x : ℂ) * f x := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hHd : ∀ x, HasDerivAt (fun y => (ψ y : ℂ) * F y)
      (((deriv ψ x : ℝ) : ℂ) * F x + (ψ x : ℂ) * f x) x := fun x =>
    (((hψ.differentiable x).hasDerivAt).ofReal_comp).mul (hF x)
  have hint1 : Integrable (fun x => ((deriv ψ x : ℝ) : ℂ) * F x) volume :=
    hψ.deriv'.integrable_mul hFc.locallyIntegrable
  have hint2 : Integrable (fun x => (ψ x : ℂ) * f x) volume :=
    hψ.integrable_mul hf.locallyIntegrable
  have h0 := MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable hHd (hint1.add hint2)
    (hψ.integrable_mul hFc.locallyIntegrable)
  rw [integral_add hint1 hint2] at h0
  exact eq_neg_of_add_eq_zero_left h0

/-! ### Integration by parts against a primitive -/

section Primitive

variable {ψ : ℝ → ℝ} {g : ℝ → ℂ}

/-- The kernel used in the Fubini argument below is integrable on the product. -/
private theorem integrable_uncurry_aux (hψ : IsTestFunction ψ) (hg : Integrable g volume) :
    Integrable (Function.uncurry
      (fun x t : ℝ => ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t))
      (volume.prod volume) := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hunc : (Function.uncurry
      (fun x t : ℝ => ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t))
      = Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1}
          (fun p => ((deriv ψ p.1 : ℝ) : ℂ) * g p.2) := by
    funext p
    by_cases h : p.2 ≤ p.1 <;> simp [Function.uncurry, Set.indicator, h, Set.mem_Iic]
  rw [hunc]
  exact (Integrable.mul_prod
    ((Complex.continuous_ofReal.comp hψ.deriv'.continuous).integrable_of_hasCompactSupport
      (hψ.deriv'.2.comp_left (g := Complex.ofReal) (by simp))) hg).indicator hmeas

/-- The integrand appearing in the integration by parts formula for a primitive is
integrable. -/
theorem integrable_deriv_mul_Iic (hψ : IsTestFunction ψ) (hg : Integrable g volume) :
    Integrable (fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * ∫ t in Set.Iic x, g t) volume := by
  refine ((integrable_uncurry_aux hψ hg).integral_prod_left).congr ?_
  filter_upwards with x
  simp only [Function.uncurry]
  rw [integral_const_mul, integral_indicator measurableSet_Iic]

/-- Integration by parts for the primitive `x ↦ ∫ t in Iic x, g t` of an integrable
function. -/
theorem integral_deriv_testFunction_mul_Iic (hψ : IsTestFunction ψ)
    (hg : Integrable g volume) :
    ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in Set.Iic x, g t) = -∫ x : ℝ, (ψ x : ℂ) * g x := by
  have hswap := MeasureTheory.integral_integral_swap (integrable_uncurry_aux hψ hg)
  have hL : ∀ x : ℝ, ∫ t : ℝ, ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t
      = ((deriv ψ x : ℝ) : ℂ) * ∫ t in Set.Iic x, g t := by
    intro x
    rw [integral_const_mul, integral_indicator measurableSet_Iic]
  have hR : ∀ t : ℝ, ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t
      = -((ψ t : ℝ) : ℂ) * g t := by
    intro t
    have he : (fun x : ℝ => ((deriv ψ x : ℝ) : ℂ) * Set.indicator (Set.Iic x) g t)
        = Set.indicator (Set.Ici t) (fun x => ((deriv ψ x : ℝ) : ℂ) * g t) := by
      funext x
      by_cases h : t ≤ x <;> simp [Set.indicator, h, Set.mem_Iic, Set.mem_Ici]
    rw [he, integral_indicator measurableSet_Ici, integral_mul_const,
      MeasureTheory.integral_Ici_eq_integral_Ioi, integral_complex_ofReal,
      HasCompactSupport.integral_Ioi_deriv_eq hψ.contDiff_one hψ.2 t]
    push_cast
    ring
  simp only [hL, hR] at hswap
  rw [hswap, ← integral_neg]
  congr 1
  funext t
  ring

/-- Integration by parts for the primitive `x ↦ ∫ t in 0..x, g t` of a locally integrable
function; equivalently, the distributional derivative of the primitive is `g`. -/
theorem integral_deriv_testFunction_mul_primitive (hψ : IsTestFunction ψ)
    (hg : LocallyIntegrable g volume) :
    ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in (0 : ℝ)..x, g t) = -∫ x : ℝ, (ψ x : ℂ) * g x := by
  obtain ⟨R₁, hR₁0, hR₁⟩ := hψ.2.exists_pos_le_norm
  obtain ⟨R₂, hR₂0, hR₂⟩ := hψ.deriv'.2.exists_pos_le_norm
  set R : ℝ := max R₁ R₂ with hRdef
  have hR0 : 0 < R := lt_of_lt_of_le hR₁0 (le_max_left _ _)
  have hψ0 : ∀ x : ℝ, R ≤ |x| → ψ x = 0 := fun x hx =>
    hR₁ x (by rw [Real.norm_eq_abs]; exact le_trans (le_max_left _ _) hx)
  have hdψ0 : ∀ x : ℝ, R ≤ |x| → deriv ψ x = 0 := fun x hx =>
    hR₂ x (by rw [Real.norm_eq_abs]; exact le_trans (le_max_right _ _) hx)
  set g₀ : ℝ → ℂ := Set.indicator (Set.Icc (-R) R) g with hg₀def
  have hg₀ : Integrable g₀ volume :=
    (hg.integrableOn_isCompact isCompact_Icc).integrable_indicator measurableSet_Icc
  set C : ℂ := ∫ t in Set.Iic (0 : ℝ), g₀ t with hC
  have hpt : ∀ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in (0 : ℝ)..x, g t)
      = ((deriv ψ x : ℝ) : ℂ) * (∫ t in Set.Iic x, g₀ t) - ((deriv ψ x : ℝ) : ℂ) * C := by
    intro x
    by_cases hx : R ≤ |x|
    · simp [hdψ0 x hx]
    · push_neg at hx
      rw [abs_lt] at hx
      have h1 : ∫ t in (0 : ℝ)..x, g t = ∫ t in (0 : ℝ)..x, g₀ t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        have htmem : t ∈ Set.Icc (-R) R := by
          rcases le_total (0 : ℝ) x with h | h
          · rw [Set.uIcc_of_le h] at ht
            exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
          · rw [Set.uIcc_of_ge h] at ht
            exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        simp [hg₀def, Set.indicator_of_mem htmem]
      have h2 : ∫ t in (0 : ℝ)..x, g₀ t
          = (∫ t in Set.Iic x, g₀ t) - ∫ t in Set.Iic (0 : ℝ), g₀ t :=
        (intervalIntegral.integral_Iic_sub_Iic hg₀.integrableOn hg₀.integrableOn).symm
      rw [h1, h2, hC]
      ring
  have hsplit : ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in (0 : ℝ)..x, g t)
      = (∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (∫ t in Set.Iic x, g₀ t))
        - ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * C := by
    rw [← integral_sub (integrable_deriv_mul_Iic hψ hg₀)
      (hψ.deriv'.integrable_mul (continuous_const.locallyIntegrable))]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hzero : ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * C = 0 := by
    rw [integral_mul_const, hψ.integral_deriv_eq_zero, zero_mul]
  have hlast : ∫ x : ℝ, (ψ x : ℂ) * g₀ x = ∫ x : ℝ, (ψ x : ℂ) * g x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : R ≤ |x|
    · simp [hψ0 x hx]
    · push_neg at hx
      rw [abs_lt] at hx
      simp [hg₀def, Set.indicator_of_mem (show x ∈ Set.Icc (-R) R from ⟨hx.1.le, hx.2.le⟩)]
  rw [hsplit, hzero, sub_zero, integral_deriv_testFunction_mul_Iic hψ hg₀, hlast]

end Primitive

/-! ### du Bois-Reymond lemmas -/

/-- A locally integrable function with vanishing distributional derivative is almost
everywhere constant. -/
theorem ae_const_of_weak_deriv_eq_zero {v : ℝ → ℂ} (hv : LocallyIntegrable v volume)
    (h : ∀ ψ : ℝ → ℝ, IsTestFunction ψ → ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * v x = 0) :
    ∃ c : ℂ, v =ᵐ[volume] fun _ => c := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_testFunction_integral_one
  set k : ℂ := ∫ x : ℝ, (ρ x : ℂ) * v x with hk
  refine ⟨k, ?_⟩
  have key : ∀ ψ : ℝ → ℝ, IsTestFunction ψ →
      ∫ x : ℝ, (ψ x : ℂ) * v x = ∫ x : ℝ, (ψ x : ℂ) * k := by
    intro ψ hψ
    set c : ℝ := ∫ x : ℝ, ψ x with hc
    have hη : IsTestFunction (fun x => ψ x - c * ρ x) :=
      ⟨hψ.1.sub (contDiff_const.mul hρ.1), hψ.2.sub hρ.2.mul_left⟩
    have hη0 : ∫ x : ℝ, (ψ x - c * ρ x) = 0 := by
      rw [integral_sub hψ.integrable (hρ.integrable.const_mul c)]
      simp [integral_const_mul, hρ1, ← hc]
    obtain ⟨θ, hθ, hθd⟩ := exists_testFunction_hasDerivAt hη hη0
    have hdθ : deriv θ = fun x => ψ x - c * ρ x := funext fun x => (hθd x).deriv
    have hz := h θ hθ
    rw [hdθ] at hz
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, sub_mul] at hz
    rw [integral_sub (hψ.integrable_mul hv)
      (by simpa [mul_assoc] using ((hρ.integrable_mul hv).const_mul (c : ℂ)))] at hz
    have h2 : ∫ x : ℝ, (c : ℂ) * (ρ x : ℂ) * v x = (c : ℂ) * k := by
      rw [hk, ← integral_const_mul]; congr 1; ext x; ring
    rw [h2, sub_eq_zero] at hz
    rw [hz, integral_mul_const, integral_complex_ofReal]
  refine ae_eq_of_integral_contDiff_smul_eq hv continuous_const.locallyIntegrable ?_
  intro g hg hgc
  simpa only [Complex.real_smul] using key g ⟨hg, hgc⟩

/-- A locally integrable function whose second distributional derivative vanishes is
almost everywhere affine. -/
theorem ae_affine_of_weak_second_deriv_eq_zero {w : ℝ → ℂ} (hw : LocallyIntegrable w volume)
    (h : ∀ φ : ℝ → ℝ, IsTestFunction φ → ∫ x : ℝ, ((deriv (deriv φ) x : ℝ) : ℂ) * w x = 0) :
    ∃ c₀ c₁ : ℂ, w =ᵐ[volume] fun x => c₀ + c₁ * x := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_testFunction_integral_one
  set k : ℂ := ∫ x : ℝ, ((deriv ρ x : ℝ) : ℂ) * w x with hk
  have key : ∀ ψ : ℝ → ℝ, IsTestFunction ψ →
      ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * w x = (∫ x : ℝ, ψ x : ℝ) * k := by
    intro ψ hψ
    set c : ℝ := ∫ x : ℝ, ψ x with hc
    have hη : IsTestFunction (fun x => ψ x - c * ρ x) :=
      ⟨hψ.1.sub (contDiff_const.mul hρ.1), hψ.2.sub hρ.2.mul_left⟩
    have hη0 : ∫ x : ℝ, (ψ x - c * ρ x) = 0 := by
      rw [integral_sub hψ.integrable (hρ.integrable.const_mul c)]
      simp [integral_const_mul, hρ1, ← hc]
    obtain ⟨θ, hθ, hθd⟩ := exists_testFunction_hasDerivAt hη hη0
    have hψeq : ψ = fun x => deriv θ x + c * ρ x := by
      funext x
      rw [(hθd x).deriv]
      ring
    have hderivψ : deriv ψ = fun x => deriv (deriv θ) x + c * deriv ρ x := by
      funext x
      have h1 : HasDerivAt (deriv θ) (deriv (deriv θ) x) x :=
        (hθ.deriv'.differentiable x).hasDerivAt
      have h2 : HasDerivAt (fun y => c * ρ y) (c * deriv ρ x) x :=
        ((hρ.differentiable x).hasDerivAt).const_mul c
      rw [hψeq]
      exact (h1.add h2).deriv
    rw [hderivψ]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, add_mul]
    rw [integral_add (hθ.deriv'.deriv'.integrable_mul hw)
      (by simpa [mul_assoc] using ((hρ.deriv'.integrable_mul hw).const_mul (c : ℂ))),
      h θ hθ, zero_add, hk, ← integral_const_mul]
    congr 1
    ext x
    ring
  have hV : ∀ ψ : ℝ → ℝ, IsTestFunction ψ →
      ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (w x + k * x) = 0 := by
    intro ψ hψ
    have hsplit : ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (w x + k * x)
        = (∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * w x)
          + ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (k * x) := by
      rw [← integral_add (hψ.deriv'.integrable_mul hw)
        (hψ.deriv'.integrable_mul
          (by fun_prop : Continuous fun x : ℝ => k * (x : ℂ)).locallyIntegrable)]
      congr 1
      ext x
      ring
    have hibp : ∫ x : ℝ, ((deriv ψ x : ℝ) : ℂ) * (k * x) = -∫ x : ℝ, (ψ x : ℂ) * k := by
      refine integral_deriv_testFunction_mul (F := fun x : ℝ => k * x) (f := fun _ => k)
        (fun x => ?_) continuous_const hψ
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul k
    rw [hsplit, hibp, key ψ hψ, integral_mul_const, integral_complex_ofReal]
    ring
  obtain ⟨c₀, hc₀⟩ := ae_const_of_weak_deriv_eq_zero
    (hw.add (by fun_prop : Continuous fun x : ℝ => k * (x : ℂ)).locallyIntegrable) hV
  refine ⟨c₀, -k, ?_⟩
  filter_upwards [hc₀] with x hx
  simp only [Pi.add_apply] at hx
  linear_combination hx

end Brockian.Weyl

