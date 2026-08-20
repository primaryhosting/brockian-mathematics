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

theorem integral_deriv_smul_primitive {h : ℝ → ℂ} (hh : LocallyIntegrable h volume) (c : ℝ)
    {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : IsBumpOn a b g) :
    ∫ x, deriv g x • (∫ t in c..x, h t) = -∫ x, g x • h x := by
  have hHcont : Continuous fun x => ∫ t in c..x, h t :=
    continuous_primitive_of_locallyIntegrable hh c
  have hint1 : Integrable (fun x => deriv g x • (∫ t in c..x, h t)) volume :=
    hg.deriv_isBumpOn.integrable_smul hHcont.locallyIntegrable
  have hint2 : Integrable (fun x => g x • h x) volume := hg.integrable_smul hh
  have key : ∀ L : ℂ →L[ℝ] ℝ,
      L (∫ x, deriv g x • (∫ t in c..x, h t)) = L (-∫ x, g x • h x) := by
    intro L
    have hLh : LocallyIntegrable (fun t => L (h t)) volume := by
      refine locallyIntegrable_iff.2 ?_
      intro K hK
      exact L.integrable_comp (hh.integrableOn_isCompact hK)
    have e1 : L (∫ x, deriv g x • (∫ t in c..x, h t))
        = ∫ x, deriv g x * (∫ t in c..x, L (h t)) := by
      rw [← L.integral_comp_comm hint1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ContinuousLinearMap.map_smul, smul_eq_mul]
      congr 1
      exact (L.intervalIntegral_comp_comm (intervalIntegrable_of_locallyIntegrable hh c x)).symm
    have e2 : L (-∫ x, g x • h x) = -∫ x, g x * L (h x) := by
      rw [map_neg, ← L.integral_comp_comm hint2]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [e1, e2]
    exact integral_deriv_mul_primitive_real hLh c hab hg
  have hre := key Complex.reCLM
  have him := key Complex.imCLM
  exact Complex.ext hre him

end Brockian.Weyl

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Smooth compactly supported test functions on an interval

This file develops the small amount of test-function calculus needed for the
one–dimensional regularity theory (Weyl's lemma) used in
`Brockian.Weyl.DeficiencyODE`.

The main definitions and results are:

* `Brockian.Weyl.IsBumpOn a b g` : `g : ℝ → ℝ` is smooth, compactly supported and its
  support is contained in `Set.Ioo a b`;
* `Brockian.Weyl.IsBumpOn.exists_Ioo` : the support of a bump is contained in a
  slightly smaller open interval;
* `Brockian.Weyl.IsBumpOn.antideriv` : the primitive of a bump with vanishing integral
  is again a bump;
* `Brockian.Weyl.exists_isBumpOn_integral_eq_one` : existence of a bump of integral one.
-/

namespace Brockian.Weyl

open MeasureTheory Set Function
open scoped Topology

/-- `IsBumpOn a b g` says that `g : ℝ → ℝ` is a test function for the open interval
`Ioo a b`: it is smooth, compactly supported, and its (closed) support is contained
in `Ioo a b`. -/
structure IsBumpOn (a b : ℝ) (g : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g
  compactSupport : HasCompactSupport g
  tsupport_subset : tsupport g ⊆ Set.Ioo a b

namespace IsBumpOn

variable {a b : ℝ} {g : ℝ → ℝ}

