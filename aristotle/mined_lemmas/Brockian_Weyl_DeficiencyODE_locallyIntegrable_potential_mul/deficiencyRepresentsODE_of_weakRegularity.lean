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

theorem deficiencyRepresentsODE_of_weakRegularity {a b : ℝ} (hab : a < b) {q : ℝ → ℝ}
    (hq : Continuous q) (lam : ℂ) (y : ℝ → ℂ) :
    InDeficiencySpace q lam a b y ↔
      ∃ u : ℝ → ℂ, IsODESolutionOn q lam (Set.Ioo a b) u ∧
        MemLp u 2 (volume.restrict (Set.Ioo a b)) ∧
        y =ᵐ[volume.restrict (Set.Ioo a b)] u := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    simp [Real.volume_Ioo]
  constructor
  · rintro ⟨hLp, hdef⟩
    have hyint : IntegrableOn y (Set.Ioo a b) volume := hLp.integrable one_le_two
    set Y : ℝ → ℂ := (Set.Ioo a b).indicator y with hYdef
    have hYint : Integrable Y volume := hyint.integrable_indicator measurableSet_Ioo
    have hYeq : ∀ x ∈ Set.Ioo a b, Y x = y x := fun x hx => Set.indicator_of_mem hx y
    have hdefY : ∀ g : ℝ → ℂ, ContDiff ℝ ∞' g → HasCompactSupport g →
        tsupport g ⊆ Set.Ioo a b →
        ∫ x, (starRingEnd ℂ) (Y x) *
          (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0 := by
      intro g h1 h2 h3
      rw [← hdef g h1 h2 h3]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      by_cases hx : x ∈ Set.Ioo a b
      · rw [hYeq x hx]
      · have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hx (h3 hc)
        have hts2 : tsupport (deriv (deriv g)) ⊆ Set.Ioo a b :=
          ((closure_minimal support_deriv_subset isClosed_closure).trans
            (closure_minimal support_deriv_subset isClosed_closure)).trans h3
        have hg2 : deriv (deriv g) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hc => hx (hts2 hc)
        rw [hg0, hg2]
        ring
    obtain ⟨u, hu, hYu⟩ := weakRegularity hab hq hYint
      (weak_of_deficiency hq hYint.locallyIntegrable hdefY)
    have hyu : y =ᵐ[volume.restrict (Set.Ioo a b)] u := by
      refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      filter_upwards [hYu] with x hx hmem
      rw [← hYeq x hmem]
      exact hx hmem
    exact ⟨u, hu, hLp.ae_eq hyu, hyu⟩
  · rintro ⟨u, hu, hLp, hyu⟩
    refine ⟨hLp.ae_eq hyu.symm, ?_⟩
    intro g h1 h2 h3
    have hyu' : ∀ᵐ x, x ∈ Set.Ioo a b → y x = u x :=
      (ae_restrict_iff' measurableSet_Ioo).1 hyu
    have hswap : ∫ x, (starRingEnd ℂ) (y x) *
        (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x)
        = ∫ x, (starRingEnd ℂ) (u x) *
          (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) := by
      refine integral_congr_ae ?_
      filter_upwards [hyu'] with x hx
      by_cases hmem : x ∈ Set.Ioo a b
      · rw [hx hmem]
      · have hg0 : g x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hmem (h3 hc)
        have hts2 : tsupport (deriv (deriv g)) ⊆ Set.Ioo a b :=
          ((closure_minimal support_deriv_subset isClosed_closure).trans
            (closure_minimal support_deriv_subset isClosed_closure)).trans h3
        have hg2 : deriv (deriv g) x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hc => hmem (hts2 hc)
        rw [hg0, hg2]
        ring
    rw [hswap]
    exact deficiency_of_isODESolution hab hq hu g h1 h2 h3

end Brockian.Weyl.DeficiencyODE

import Brockian.Weyl.TestFunctions

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Distributions with vanishing first or second derivative on an interval

Let `f : ℝ → E` be locally integrable.

* `Brockian.Weyl.ae_eq_const_of_integral_deriv_smul_eq_zero` (du Bois-Reymond): if
  `∫ g' • f = 0` for every test function `g` supported in `Ioo a b`, then `f` is a.e.
  constant on `Ioo a b`.
* `Brockian.Weyl.ae_eq_affine_of_integral_deriv2_smul_eq_zero`: if `∫ g'' • f = 0` for
  every test function `g` supported in `Ioo a b`, then `f` is a.e. affine on `Ioo a b`.
-/

namespace Brockian.Weyl

open MeasureTheory Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bump function is integrable. -/
