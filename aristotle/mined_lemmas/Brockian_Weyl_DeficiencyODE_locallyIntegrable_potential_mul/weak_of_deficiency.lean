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

theorem weak_of_deficiency (hq : Continuous q) {y : ℝ → ℂ}
    (hy : LocallyIntegrable y volume)
    (hdef : ∀ g : ℝ → ℂ, ContDiff ℝ ∞' g → HasCompactSupport g → tsupport g ⊆ Set.Ioo a b →
      ∫ x, (starRingEnd ℂ) (y x) *
        (-(deriv (deriv g) x) + (q x : ℂ) * g x - (starRingEnd ℂ) lam * g x) = 0) :
    ∀ g : ℝ → ℝ, IsBumpOn a b g →
      ∫ x, deriv (deriv g) x • y x = ∫ x, g x • (((q x : ℂ) - lam) * y x) := by
  intro g hg
  set gc : ℝ → ℂ := fun x => (g x : ℂ) with hgc
  have hd1 : ∀ x, HasDerivAt gc (((deriv g x : ℝ) : ℂ)) x := fun x => (hg.hasDerivAt x).ofReal_comp
  have hderiv_gc : deriv gc = fun x => ((deriv g x : ℝ) : ℂ) := funext fun x => (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (fun x => ((deriv g x : ℝ) : ℂ)) (((deriv (deriv g) x : ℝ) : ℂ)) x :=
    fun x => (hg.deriv_isBumpOn.hasDerivAt x).ofReal_comp
  have hderiv2_gc : deriv (deriv gc) = fun x => ((deriv (deriv g) x : ℝ) : ℂ) := by
    rw [hderiv_gc]
    exact funext fun x => (hd2 x).deriv
  have hsmooth : ContDiff ℝ ∞' gc := Complex.ofRealCLM.contDiff.comp hg.smooth
  have hsupp : Function.support gc = Function.support g := by
    ext x
    simp [hgc]
  have htsupp : tsupport gc = tsupport g := by
    unfold tsupport
    rw [hsupp]
  have hcs : HasCompactSupport gc := by
    rw [HasCompactSupport, htsupp]
    exact hg.compactSupport
  have hts : tsupport gc ⊆ Set.Ioo a b := by
    rw [htsupp]
    exact hg.tsupport_subset
  have h0 := hdef gc hsmooth hcs hts
  rw [hderiv2_gc] at h0
  have hconj : (starRingEnd ℂ) (∫ x, (starRingEnd ℂ) (y x) *
      (-((deriv (deriv g) x : ℝ) : ℂ) + (q x : ℂ) * gc x
        - (starRingEnd ℂ) lam * gc x)) = 0 := by
    rw [h0]
    simp
  rw [← integral_conj] at hconj
  simp only [map_mul, map_sub, map_add, map_neg, Complex.conj_conj, Complex.conj_ofReal,
    hgc] at hconj
  -- `hconj : ∫ x, y x * (-(deriv (deriv g) x) + q x * g x - lam * g x) = 0`
  have hA : Integrable (fun x => deriv (deriv g) x • y x) volume :=
    hg.deriv_isBumpOn.deriv_isBumpOn.integrable_smul hy
  have hB : Integrable (fun x => g x • (((q x : ℂ) - lam) * y x)) volume :=
    hg.integrable_smul (locallyIntegrable_potential_mul hq hy)
  have hpt : ∀ x, y x * (-((deriv (deriv g) x : ℝ) : ℂ) + (q x : ℂ) * (g x : ℂ)
      - lam * (g x : ℂ)) = -(deriv (deriv g) x • y x) + g x • (((q x : ℂ) - lam) * y x) := by
    intro x
    simp only [Complex.real_smul]
    ring
  simp_rw [hpt] at hconj
  have hAneg : Integrable (fun x => -(deriv (deriv g) x • y x)) volume := hA.neg
  rw [integral_add hAneg hB] at hconj
  simp only [integral_neg] at hconj
  exact neg_add_eq_zero.mp hconj

end Auxiliary

/-- **Weyl's lemma in one dimension** (elliptic regularity for `-u'' + q u = lam u`).

If `y` is integrable and satisfies the differential equation `-y'' + q y = lam y` in the
distributional sense on `(a, b)`, then `y` agrees almost everywhere on `(a, b)` with a
classical (twice differentiable) solution of the equation.

This is the regularity statement that used to be assumed as a hypothesis in
`deficiencyRepresentsODE_of_weakRegularity`; it is proved here, which makes that theorem
unconditional. -/
