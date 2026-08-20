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

import Brockian.Weyl.Primitive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Deficiency elements of a Sturm–Liouville operator are genuine ODE solutions

Let `q : ℝ → ℝ` be a continuous potential on an interval `(a, b)` and let `lam : ℂ`.  The
*minimal operator* associated with the formally symmetric differential expression
`τ u = -u'' + q u` is the restriction of `τ` to smooth compactly supported functions in
`(a, b)`.  A function `y ∈ L²(a, b)` lies in the deficiency space of the minimal operator
at `lam` exactly when it is orthogonal to the range of `τ - conj lam` on test functions,
that is when
`∫ conj (y x) * (-(g'' x) + q x * g x - conj lam * g x) = 0`
for every test function `g` supported in `(a, b)`; see `InDeficiencySpace`.

The main theorem `deficiencyRepresentsODE_of_weakRegularity` states that the deficiency
space is exactly the space of `L²` solutions of the ordinary differential equation
`-u'' + q u = lam * u`, i.e. every deficiency element is (a.e. equal to) a genuine, twice
differentiable, classical solution of the ODE.

The hard direction rests on the one-dimensional elliptic regularity statement
`weakRegularity` (Weyl's lemma): a locally integrable distributional solution of
`-y'' + q y = lam y` agrees a.e. with a classical solution.  It is proved here, so the
main theorem is unconditional.
-/

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory Set Function Brockian.Weyl

/-- The smoothness exponent `∞`. -/
local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- `IsODESolutionOn q lam s u` says that `u` is a classical solution of
`-u'' + q u = lam * u` on the set `s`: `u` is differentiable with a differentiable
derivative `u'` and `u'' = (q - lam) * u` on `s`. -/

theorem weakRegularity {a b : ℝ} (hab : a < b) {q : ℝ → ℝ} (hq : Continuous q) {lam : ℂ}
    {y : ℝ → ℂ} (hy : Integrable y volume)
    (hweak : ∀ g : ℝ → ℝ, IsBumpOn a b g →
      ∫ x, deriv (deriv g) x • y x = ∫ x, g x • (((q x : ℂ) - lam) * y x)) :
    ∃ u : ℝ → ℂ, IsODESolutionOn q lam (Set.Ioo a b) u ∧
      ∀ᵐ x, x ∈ Set.Ioo a b → y x = u x := by
  set I : Set ℝ := Set.Ioo a b with hI
  -- the right-hand side of the equation, truncated to the interval
  set h : ℝ → ℂ := I.indicator (fun t => ((q t : ℂ) - lam) * y t) with hhdef
  have hqy : LocallyIntegrable (fun t => ((q t : ℂ) - lam) * y t) volume :=
    locallyIntegrable_potential_mul hq hy.locallyIntegrable
  have hhint : Integrable h volume := by
    have h1 : IntegrableOn (fun t => ((q t : ℂ) - lam) * y t) I volume :=
      (hqy.integrableOn_isCompact (isCompact_Icc (a := a) (b := b))).mono_set
        Set.Ioo_subset_Icc_self
    exact h1.integrable_indicator measurableSet_Ioo
  -- the double primitive of `h`
  set c : ℝ := (a + b) / 2 with hc
  have hcI : c ∈ I := by
    constructor <;> · rw [hc]; linarith
  set H : ℝ → ℂ := fun x => ∫ t in c..x, h t with hHdef
  have hHcont : Continuous H := hhint.continuous_primitive c
  set G : ℝ → ℂ := fun x => ∫ t in c..x, H t with hGdef
  have hGderiv : ∀ x, HasDerivAt G (H x) x := fun x =>
    (hHcont.integral_hasStrictDerivAt c x).hasDerivAt
  have hGdiff : Differentiable ℝ G := fun x => (hGderiv x).differentiableAt
  have hGcont : Continuous G := hGdiff.continuous
  -- the double primitive solves the equation distributionally
  have key1 : ∀ g : ℝ → ℝ, IsBumpOn a b g →
      ∫ x, deriv (deriv g) x • G x = ∫ x, g x • h x := by
    intro g hg
    have e1 : ∫ x, deriv (deriv g) x • G x = -∫ x, deriv g x • H x := by
      simp only [hGdef]
      exact integral_deriv_smul_primitive hHcont.locallyIntegrable c hab hg.deriv_isBumpOn
    have e2 : ∫ x, deriv g x • H x = -∫ x, g x • h x := by
      simp only [hHdef]
      exact integral_deriv_smul_primitive hhint.locallyIntegrable c hab hg
    rw [e1, e2, neg_neg]
  -- hence `y - G` has vanishing second distributional derivative
  have key2 : ∀ g : ℝ → ℝ, IsBumpOn a b g → ∫ x, deriv (deriv g) x • (y x - G x) = 0 := by
    intro g hg
    have hint1 : Integrable (fun x => deriv (deriv g) x • y x) volume :=
      hg.deriv_isBumpOn.deriv_isBumpOn.integrable_smul hy.locallyIntegrable
    have hint2 : Integrable (fun x => deriv (deriv g) x • G x) volume :=
      hg.deriv_isBumpOn.deriv_isBumpOn.integrable_smul hGcont.locallyIntegrable
    have hsplit : ∫ x, deriv (deriv g) x • (y x - G x)
        = (∫ x, deriv (deriv g) x • y x) - ∫ x, deriv (deriv g) x • G x := by
      simp_rw [smul_sub]
      exact integral_sub hint1 hint2
    have hgh : ∀ x, g x • h x = g x • (((q x : ℂ) - lam) * y x) := by
      intro x
      by_cases hx : x ∈ I
      · rw [hhdef, Set.indicator_of_mem hx]
      · rw [hg.zero_of_notMem hx]
        simp
    rw [hsplit, key1 g hg, hweak g hg]
    simp_rw [hgh]
    exact sub_self _
  have hfloc : LocallyIntegrable (fun x => y x - G x) volume :=
    hy.locallyIntegrable.sub hGcont.locallyIntegrable
  obtain ⟨A, B, hAB⟩ := ae_eq_affine_of_integral_deriv2_smul_eq_zero hab hfloc key2
  -- the candidate classical solution
  set u : ℝ → ℂ := fun x => G x + (x • A + B) with hudef
  have hucont : Continuous u :=
    hGcont.add ((continuous_id.smul continuous_const).add continuous_const)
  have hyu : ∀ᵐ x, x ∈ I → y x = u x := by
    filter_upwards [hAB] with x hx hmem
    have hx' := hx hmem
    rw [hudef]
    simp only
    rw [← hx']
    abel
  have hKcont : Continuous (fun t => ((q t : ℂ) - lam) * u t) :=
    ((Complex.continuous_ofReal.comp hq).sub continuous_const).mul hucont
  have hphi : ∀ z, HasDerivAt (fun x => ∫ t in c..x, ((q t : ℂ) - lam) * u t)
      (((q z : ℂ) - lam) * u z) z := fun z => (hKcont.integral_hasStrictDerivAt c z).hasDerivAt
  have hHphi : Set.EqOn H (fun x => ∫ t in c..x, ((q t : ℂ) - lam) * u t) I := by
    intro z hz
    simp only [hHdef]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hyu] with t ht htmem
    have htI : t ∈ I :=
      Set.OrdConnected.uIcc_subset Set.ordConnected_Ioo hcI hz (Set.uIoc_subset_uIcc htmem)
    rw [hhdef, Set.indicator_of_mem htI, ht htI]
  have hHderiv : ∀ x ∈ I, HasDerivAt H (((q x : ℂ) - lam) * u x) x := by
    intro x hx
    exact (hphi x).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx.1 hx.2) hHphi)
  refine ⟨u, ⟨fun x => H x + A, ?_, ?_⟩, hyu⟩
  · intro x _
    have h1 : HasDerivAt (fun x : ℝ => x • A + B) A x := by
      simpa using ((hasDerivAt_id x).smul_const A).add_const B
    simpa [hudef] using (hGderiv x).add h1
  · intro x hx
    simpa using (hHderiv x hx).add_const A

set_option maxRecDepth 8000 in
/-- A classical solution of `-u'' + q u = lam u` on `(a, b)` satisfies the deficiency
identity: it is orthogonal to `(τ - conj lam) g` for every test function `g`. -/
