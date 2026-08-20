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

theorem integral_deriv_mul_primitive_real {h : ℝ → ℝ} (hh : LocallyIntegrable h volume) (c : ℝ)
    {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : IsBumpOn a b g) :
    ∫ x, deriv g x * (∫ t in c..x, h t) = -∫ x, g x * h x := by
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hsub⟩ := hg.exists_Ioo hab
  have hgz : ∀ x, x ∉ Set.Ioo a₀ b₀ → g x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsub hx')
  have hdz : ∀ x, x ∉ Set.Ioo a₀ b₀ → deriv g x = 0 := by
    intro x hx
    have hts : tsupport (deriv g) ⊆ Set.Ioo a₀ b₀ :=
      (closure_minimal support_deriv_subset isClosed_closure).trans hsub
    exact image_eq_zero_of_notMem_tsupport fun hx' => hx (hts hx')
  set H : ℝ → ℝ := fun x => ∫ t in c..x, h t with hH
  have hHac : AbsolutelyContinuousOnInterval H a₀ b₀ :=
    absolutelyContinuousOnInterval_primitive hh c a₀ b₀
  have hgac : AbsolutelyContinuousOnInterval g a₀ b₀ := hg.absolutelyContinuousOnInterval a₀ b₀
  have hparts := hHac.integral_mul_deriv_eq_deriv_mul hgac
  have hb : g b₀ = 0 := hgz b₀ (by simp)
  have ha : g a₀ = 0 := hgz a₀ (by simp)
  rw [hb, ha] at hparts
  have hderivH : ∀ᵐ x : ℝ, deriv H x = h x := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hh] with x hx
    exact (hx c).deriv
  have hcongr : ∫ x in a₀..b₀, deriv H x * g x = ∫ x in a₀..b₀, h x * g x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderivH] with x hx _
    rw [hx]
  rw [hcongr] at hparts
  simp only [mul_zero, sub_zero, zero_sub] at hparts
  have hL : ∫ x, deriv g x * H x = ∫ x in a₀..b₀, deriv g x * H x := by
    refine integral_eq_intervalIntegral hab₀.le ?_
    intro x hx
    have : deriv g x = 0 := hdz x fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)
    simp [this]
  have hR : ∫ x, g x * h x = ∫ x in a₀..b₀, g x * h x := by
    refine integral_eq_intervalIntegral hab₀.le ?_
    intro x hx
    have : g x = 0 := hgz x fun hmem => hx (Set.Ioo_subset_Ioc_self hmem)
    simp [this]
  rw [hL, hR]
  have hcomm1 : ∫ x in a₀..b₀, deriv g x * H x = ∫ x in a₀..b₀, H x * deriv g x := by
    simp_rw [mul_comm]
  have hcomm2 : ∫ x in a₀..b₀, g x * h x = ∫ x in a₀..b₀, h x * g x := by
    simp_rw [mul_comm]
  rw [hcomm1, hcomm2, hparts]

/-- The distributional derivative of the primitive of a locally integrable complex function
is the function itself. -/
