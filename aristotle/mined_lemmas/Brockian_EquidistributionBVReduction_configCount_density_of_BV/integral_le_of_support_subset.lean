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
# Equidistribution and the bounded-variation reduction for configuration counts

Let `u : ℕ → ℝ` be a sequence which is *equidistributed* in the unit interval, in the sense
that averages of continuous test functions along `u` converge to the corresponding integral
over `[0,1]` (`Brockian.EquidistributionBVReduction.Equidistributed`).

The main result, `Brockian.EquidistributionBVReduction.configCount_density_of_BV`, upgrades
this from continuous test functions to the indicator of an interval `[a, b) ⊆ [0,1]`, which is
the basic function of bounded variation: the number of indices `n < N` with `u n ∈ [a, b)`
has density `b - a`.

The proof is the usual sandwich argument: the indicator of `[a, b)` is squeezed between two
continuous functions (produced by Urysohn's lemma) whose integrals differ from `b - a` by an
arbitrarily small amount.
-/

open MeasureTheory Set Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

open Classical in
/-- `configCount u S N` is the number of indices `n < N` for which `u n` lies in `S`. -/

lemma integral_le_of_support_subset (f : ℝ → ℝ) (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1) {p q : ℝ} (hpq : p ≤ q) (hsupp : ∀ x ∉ Ioo p q, f x = 0) :
    (∫ x in (0 : ℝ)..1, f x) ≤ q - p := by
  have hint : Integrable f volume := by
    refine hf.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := p) (b := q)) ?_
    intro x hx
    exact hsupp x fun hx' => hx (Ioo_subset_Icc_self hx')
  have hbound : (∫ x in Ioo p q, f x) ≤ ∫ _x in Ioo p q, (1 : ℝ) :=
    setIntegral_mono_on hint.integrableOn
      (integrableOn_const (by simp [Real.volume_Ioo])) measurableSet_Ioo fun x _ => h1 x
  have hconst : (∫ _x in Ioo p q, (1 : ℝ)) = q - p := by
    rw [setIntegral_const]
    simp [Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr hpq)]
  calc (∫ x in (0 : ℝ)..1, f x) = ∫ x in Ioc (0 : ℝ) 1, f x :=
        intervalIntegral.integral_of_le zero_le_one
    _ ≤ ∫ x, f x := setIntegral_le_integral hint (Filter.Eventually.of_forall h0)
    _ = ∫ x in Ioo p q, f x := (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    _ ≤ ∫ _x in Ioo p q, (1 : ℝ) := hbound
    _ = q - p := hconst

/-- A nonnegative continuous function which is at least `1` on `[c, d] ⊆ (0,1]` has integral
over `[0,1]` at least `d - c`. -/
