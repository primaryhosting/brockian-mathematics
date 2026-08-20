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

lemma exists_lower_sandwich {a b eps : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (heps : 0 < eps)
    (hgap : a + eps ≤ b - eps) (hsmall : b - a + 2 * eps ≤ 1) :
    ∃ g : C(UnitAddCircle, ℝ),
      (∀ x : ℝ, g (x : UnitAddCircle) ≤ (if Int.fract x ∈ Ico a b then (1 : ℝ) else 0)) ∧
      (b - a) - 2 * eps ≤ ∫ x : UnitAddCircle, g x := by
  set c : ℝ := a - 2 * eps with hc
  set G : ℝ → ℝ := trapLower a b eps with hGdef
  have hend : G c = G (c + 1) := by
    rw [hGdef, trapLower_eq_zero heps (Or.inl (by rw [hc]; linarith)),
      trapLower_eq_zero heps (Or.inr (by rw [hc]; linarith))]
  have hcont : Continuous (AddCircle.liftIco 1 c G) :=
    AddCircle.liftIco_continuous (by simpa using hend) ((trapLower_cont a b eps).continuousOn)
  refine ⟨⟨AddCircle.liftIco 1 c G, hcont⟩, ?_, ?_⟩
  · intro x
    show AddCircle.liftIco 1 c G ((x : ℝ) : UnitAddCircle) ≤ _
    rw [liftIco_coe]
    set r : ℝ := Int.fract (x - c) + c with hr
    by_cases hx : Int.fract x ∈ Ico a b
    · rw [if_pos hx]; exact trapLower_le_one _ _ _ _
    · rw [if_neg hx]
      have hfr : Int.fract r = Int.fract x := fract_rep c x
      have hG0 : G r = 0 := by
        rcases le_or_gt r a with h | h
        · exact trapLower_eq_zero heps (Or.inl h)
        rcases le_or_gt b r with h2 | h2
        · exact trapLower_eq_zero heps (Or.inr h2)
        · exfalso
          have hr0 : 0 ≤ r := le_trans ha h.le
          have hr1 : r < 1 := lt_of_lt_of_le h2 hb
          have hrr : Int.fract r = r := Int.fract_eq_self.mpr ⟨hr0, hr1⟩
          rw [hfr] at hrr
          exact hx (by rw [hrr]; exact ⟨h.le, h2⟩)
      rw [hG0]
  · show (b - a) - 2 * eps ≤ ∫ x : UnitAddCircle, AddCircle.liftIco 1 c G x
    rw [integral_liftIco c G hend]
    have h := le_integral_of_ge_one G (trapLower_cont a b eps) c (a + eps) (b - eps)
      (by rw [hc]; linarith) hgap (by rw [hc]; linarith)
      (fun x => trapLower_nonneg _ _ _ _)
      (fun x hx => le_of_eq (trapLower_eq_one heps hx.1 hx.2).symm)
    linarith

/-- The configuration count written as a sum of indicators. -/
