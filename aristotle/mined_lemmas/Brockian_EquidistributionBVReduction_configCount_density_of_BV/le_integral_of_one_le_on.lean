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

lemma le_integral_of_one_le_on (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ x, 0 ≤ g x)
    {c d : ℝ} (hcd : c ≤ d) (hc : 0 < c) (hd : d ≤ 1) (h1 : ∀ x ∈ Icc c d, (1 : ℝ) ≤ g x) :
    d - c ≤ ∫ x in (0 : ℝ)..1, g x := by
  have hsub : Icc c d ⊆ Ioc (0 : ℝ) 1 := fun x hx => ⟨lt_of_lt_of_le hc hx.1, hx.2.trans hd⟩
  have hconst : (∫ _x in Icc c d, (1 : ℝ)) = d - c := by
    rw [setIntegral_const]
    simp [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr hcd)]
  have hstep1 : (∫ _x in Icc c d, (1 : ℝ)) ≤ ∫ x in Icc c d, g x :=
    setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc]))
      hg.integrableOn_Icc measurableSet_Icc fun x hx => h1 x hx
  have hstep2 : (∫ x in Icc c d, g x) ≤ ∫ x in Ioc (0 : ℝ) 1, g x :=
    setIntegral_mono_set hg.integrableOn_Ioc (Filter.Eventually.of_forall h0)
      (HasSubset.Subset.eventuallyLE hsub)
  rw [intervalIntegral.integral_of_le zero_le_one, ← hconst]
  exact hstep1.trans hstep2

/-- Eventually, the configuration density for `[a, b)` is bounded above by `b - a + 3δ`. -/
