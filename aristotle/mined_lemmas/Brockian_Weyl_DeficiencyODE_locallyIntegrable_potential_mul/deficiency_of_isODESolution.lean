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

theorem deficiency_of_isODESolution {a b : ℝ} (hab : a < b) {q : ℝ → ℝ} (hq : Continuous q)
    {lam : ℂ} {u : ℝ → ℂ} (hu : IsODESolutionOn q lam (Set.Ioo a b) u) :
    ∀ g : ℝ → ℂ, ContDiff ℝ ∞' g → HasCompactSupport g → tsupport g ⊆ Set.Ioo a b →
      ∫ x, (starRingEnd ℂ) (u x) *
        (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0 := by
  obtain ⟨u', hu1, hu2⟩ := hu
  intro g hgs hgc hgt
  set v : ℝ → ℂ := fun x => (starRingEnd ℂ) (u x) with hv
  set v' : ℝ → ℂ := fun x => (starRingEnd ℂ) (u' x) with hv'
  set w : ℝ → ℂ := fun x => ((q x : ℂ) - (starRingEnd ℂ) lam) * v x with hw
  have hv1 : ∀ x ∈ Set.Ioo a b, HasDerivAt v (v' x) x := fun x hx => (hu1 x hx).star
  have hv2 : ∀ x ∈ Set.Ioo a b, HasDerivAt v' (w x) x := by
    intro x hx
    have h := (hu2 x hx).star
    have hstar : star (((q x : ℂ) - lam) * u x) = w x := by
      show star (((q x : ℂ) - lam) * u x)
        = ((q x : ℂ) - (starRingEnd ℂ) lam) * (starRingEnd ℂ) (u x)
      rw [star_mul', star_sub]
      simp [mul_comm]
    rw [hstar] at h
    exact h
  -- derivatives of the test function
  have hgd1 : ∀ x, HasDerivAt g (deriv g x) x := fun x =>
    (hgs.differentiable (by simp) x).hasDerivAt
  have hgs1 : ContDiff ℝ ∞' (deriv g) := (contDiff_infty_iff_deriv.1 hgs).2
  have hgd2 : ∀ x, HasDerivAt (deriv g) (deriv (deriv g) x) x := fun x =>
    (hgs1.differentiable (by simp) x).hasDerivAt
  have hgc1 : Continuous (deriv g) := hgs1.continuous
  have hgc2 : Continuous (deriv (deriv g)) := (contDiff_infty_iff_deriv.1 hgs1).2.continuous
  -- localize
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := exists_Ioo_of_isCompact hab hgc hgt
  have hgz : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hsub hc)
  have hts1 : tsupport (deriv g) ⊆ Set.Ioo a₀ b₀ :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hsub
  have hd1z : ∀ x, x ∉ Set.Ioo a₀ b₀ → deriv g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hts1 hc)
  have hts2 : tsupport (deriv (deriv g)) ⊆ Set.Ioo a₀ b₀ :=
    (closure_minimal support_deriv_subset isClosed_closure).trans hts1
  have hd2z : ∀ x, x ∉ Set.Ioo a₀ b₀ → deriv (deriv g) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hc => hx (hts2 hc)
  have huIcc : Set.uIcc a₀ b₀ = Set.Icc a₀ b₀ := Set.uIcc_of_le hab₀.le
  have hIcc : Set.Icc a₀ b₀ ⊆ Set.Ioo a b := Set.Icc_subset_Ioo ha₀ hb₀
  have hmem : ∀ x ∈ Set.uIcc a₀ b₀, x ∈ Set.Ioo a b := by
    intro x hx
    exact hIcc (by rwa [huIcc] at hx)
  have hvcont : ContinuousOn v (Set.uIcc a₀ b₀) := fun x hx =>
    ((hv1 x (hmem x hx)).continuousAt).continuousWithinAt
  have hv'cont : ContinuousOn v' (Set.uIcc a₀ b₀) := fun x hx =>
    ((hv2 x (hmem x hx)).continuousAt).continuousWithinAt
  have hwcont : ContinuousOn w (Set.uIcc a₀ b₀) := by
    have h1 : ContinuousOn (fun x : ℝ => ((q x : ℂ) - (starRingEnd ℂ) lam))
        (Set.uIcc a₀ b₀) :=
      ((Complex.continuous_ofReal.comp hq).sub continuous_const).continuousOn
    exact h1.mul hvcont
  have hv'int : IntervalIntegrable v' volume a₀ b₀ := hv'cont.intervalIntegrable
  have hwint : IntervalIntegrable w volume a₀ b₀ := hwcont.intervalIntegrable
  -- two integrations by parts
  have hpartsA : ∫ x in a₀..b₀, v x * deriv (deriv g) x
      = v b₀ * deriv g b₀ - v a₀ * deriv g a₀ - ∫ x in a₀..b₀, v' x * deriv g x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := v) (u' := v') (v := deriv g)
      (v' := deriv (deriv g)) (fun x hx => hv1 x (hmem x hx)) (fun x _ => hgd2 x)
      hv'int (hgc2.intervalIntegrable _ _)
  have hpartsB : ∫ x in a₀..b₀, v' x * deriv g x
      = v' b₀ * g b₀ - v' a₀ * g a₀ - ∫ x in a₀..b₀, w x * g x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := v') (u' := w) (v := g)
      (v' := deriv g) (fun x hx => hv2 x (hmem x hx)) (fun x _ => hgd1 x)
      hwint (hgc1.intervalIntegrable _ _)
  rw [hgz a₀ (by simp), hgz b₀ (by simp)] at hpartsB
  rw [hd1z a₀ (by simp), hd1z b₀ (by simp)] at hpartsA
  simp only [mul_zero, sub_zero, zero_sub] at hpartsA hpartsB
  rw [hpartsB, neg_neg] at hpartsA
  -- assemble
  have hzero : ∀ x ∉ Set.Ioc a₀ b₀,
      v x * (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0 := by
    intro x hx
    have hx' : x ∉ Set.Ioo a₀ b₀ := fun hc => hx (Set.Ioo_subset_Ioc_self hc)
    rw [hgz x hx', hd2z x hx']
    ring
  rw [integral_eq_intervalIntegral hab₀.le hzero]
  have hptwise : ∀ x, v x * (-(deriv (deriv g) x) + (q x : ℂ) * g x
      - (starRingEnd ℂ) lam * g x) = -(v x * deriv (deriv g) x) + w x * g x := by
    intro x
    rw [hw]
    ring
  simp_rw [hptwise]
  have hi1 : IntervalIntegrable (fun x => -(v x * deriv (deriv g) x)) volume a₀ b₀ :=
    ((hvcont.mul hgc2.continuousOn).neg).intervalIntegrable
  have hi2 : IntervalIntegrable (fun x => w x * g x) volume a₀ b₀ :=
    (hwcont.mul (hgs.continuous.continuousOn)).intervalIntegrable
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_neg, hpartsA]
  ring

/-- **Deficiency elements are ODE solutions.**  A function `y` belongs to the deficiency
space of the minimal Sturm–Liouville operator `-u'' + q u` at `lam` on `(a, b)` if and
only if it agrees almost everywhere with an `L²` classical solution of the differential
equation `-u'' + q u = lam u`. -/
