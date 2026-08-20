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

lemma eventually_le_configCount_div (u : ℕ → ℝ) (hequi : Equidistributed u) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (b - a) - 3 * δ ≤ (configCount u (Ico a b) N : ℝ) / N := by
  by_cases hsmall : b - a ≤ 2 * δ
  · filter_upwards with N
    have h0 : (0 : ℝ) ≤ (configCount u (Ico a b) N : ℝ) / N := by positivity
    linarith
  push_neg at hsmall
  obtain ⟨g, hg1, hg0, -, hgmem⟩ :=
    exists_continuous_one_zero_of_isCompact (X := ℝ) (s := Icc (a + δ) (b - δ))
      (t := (Ioo a b)ᶜ) isCompact_Icc isOpen_Ioo.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.mpr
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have hInt : (b - a) - 2 * δ ≤ ∫ x in (0 : ℝ)..1, g x := by
    have := le_integral_of_one_le_on (g := fun x => g x) g.continuous (fun x => (hgmem x).1)
      (c := a + δ) (d := b - δ) (by linarith) (by linarith) (by linarith)
      (fun x hx => by
        have h := hg1 hx
        simp only [Pi.one_apply] at h
        simp [h])
    linarith [this]
  have hev : ∀ᶠ N : ℕ in atTop,
      (∫ x in (0 : ℝ)..1, g x) - δ < (∑ n ∈ Finset.range N, g (u n)) / N :=
    Filter.Tendsto.eventually_const_lt (by linarith) (hequi (fun x => g x) g.continuous)
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hcount : ∑ n ∈ Finset.range N, g (u n) ≤ (configCount u (Ico a b) N : ℝ) :=
    sum_le_configCount u _ N _ (fun x => (hgmem x).2)
      (fun x hx => by
        refine hg0 ?_
        intro hx'
        exact hx ⟨le_of_lt hx'.1, hx'.2⟩)
  have : (∑ n ∈ Finset.range N, g (u n)) / N ≤ (configCount u (Ico a b) N : ℝ) / N := by
    gcongr
  linarith [hN, this]

/-- **Configuration counting density from equidistribution.**

If `u` is equidistributed in `[0,1]` (against continuous test functions) then, for any
subinterval `[a, b) ⊆ [0, 1]`, the proportion of indices `n < N` with `u n ∈ [a, b)` tends to
`b - a`.  This is the reduction from continuous test functions to the basic test functions of
bounded variation, namely indicators of intervals. -/
