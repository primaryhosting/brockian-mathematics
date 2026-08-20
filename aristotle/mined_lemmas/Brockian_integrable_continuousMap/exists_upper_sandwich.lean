import Brockian.EquidistributionBVReduction

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

import Mathlib

/-!
# Equidistribution of `n • α` and the reduction of configuration counts to the main term

For an irrational `α`, the configuration count

`configCount α a b N = #{ n < N : Int.fract (n * α) ∈ [a, b) }`

is asymptotic to its main term `mainTerm a b N = (b - a) * N`.

The analytic input (Weyl equidistribution of the sequence `n • α` on the circle `ℝ / ℤ`)
is proved here from scratch, so the final statement
`configCount_over_main_tendsto` is unconditional.

The proof proceeds by:
* computing the Birkhoff averages of the Fourier monomials `fourier k` along the orbit
  (geometric sums, `avg_fourier_tendsto`);
* extending to all continuous functions by Stone--Weierstrass (`avg_continuous_tendsto`);
* sandwiching the indicator of an arc between continuous piecewise-linear functions
  (a bounded-variation reduction) to obtain the counting asymptotics.
-/

open Filter MeasureTheory Set Topology Complex
open scoped BigOperators

set_option autoImplicit false

namespace Brockian

namespace EquidistributionBVReduction

noncomputable section

local instance isProbabilityMeasure_volume_unitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- The point `n * α` of the circle `ℝ / ℤ`. -/

lemma exists_upper_sandwich {a b eps : ℝ} (hab : a ≤ b) (heps : 0 < eps)
    (hsmall : b - a + 3 * eps ≤ 1) :
    ∃ h : C(UnitAddCircle, ℝ),
      (∀ x : ℝ, (if Int.fract x ∈ Ico a b then (1 : ℝ) else 0) ≤ h (x : UnitAddCircle)) ∧
      (∫ x : UnitAddCircle, h x) ≤ (b - a) + 2 * eps := by
  set c : ℝ := a - 2 * eps with hc
  set F : ℝ → ℝ := trapUpper a b eps with hFdef
  have hend : F c = F (c + 1) := by
    rw [hFdef, trapUpper_eq_zero_left heps (by rw [hc]; linarith),
      trapUpper_eq_zero_right heps (by rw [hc]; linarith)]
  have hcont : Continuous (AddCircle.liftIco 1 c F) :=
    AddCircle.liftIco_continuous (by simpa using hend) ((trapUpper_cont a b eps).continuousOn)
  refine ⟨⟨AddCircle.liftIco 1 c F, hcont⟩, ?_, ?_⟩
  · intro x
    by_cases hx : Int.fract x ∈ Ico a b
    · rw [if_pos hx]
      have hxc : ((x : ℝ) : UnitAddCircle) = ((Int.fract x : ℝ) : UnitAddCircle) := by
        rw [Int.fract]; simp
      have hmem : Int.fract x ∈ Ico c (c + 1) :=
        ⟨by rw [hc]; linarith [hx.1], by rw [hc]; linarith [hx.2]⟩
      show 1 ≤ AddCircle.liftIco 1 c F ((x : ℝ) : UnitAddCircle)
      rw [hxc, AddCircle.liftIco_coe_apply (by simpa using hmem), hFdef,
        trapUpper_eq_one heps hx.1 hx.2.le]
    · rw [if_neg hx]
      show 0 ≤ AddCircle.liftIco 1 c F ((x : ℝ) : UnitAddCircle)
      rw [liftIco_coe]
      exact trapUpper_nonneg _ _ _ _
  · show (∫ x : UnitAddCircle, AddCircle.liftIco 1 c F x) ≤ (b - a) + 2 * eps
    rw [integral_liftIco c F hend]
    have h := integral_le_of_support F (trapUpper_cont a b eps) c (a - eps) (b + eps)
      (by rw [hc]; linarith) (by linarith) (by rw [hc]; linarith)
      (fun x hx => trapUpper_eq_zero_left heps hx.2)
      (fun x hx => trapUpper_eq_zero_right heps hx.1)
      (fun x => trapUpper_le_one _ _ _ _)
    linarith

/-- A continuous function on the circle dominated by the indicator of the arc `[a, b)`,
with integral at least `(b - a) - 2 * eps`. -/
