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

lemma eventually_configCount_div_le (u : ℕ → ℝ) (hequi : Equidistributed u) {a b : ℝ}
    (hab : a ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (configCount u (Ico a b) N : ℝ) / N ≤ (b - a) + 3 * δ := by
  obtain ⟨f, hf1, hf0, -, hfmem⟩ :=
    exists_continuous_one_zero_of_isCompact (X := ℝ) (s := Icc a b)
      (t := (Ioo (a - δ) (b + δ))ᶜ) isCompact_Icc isOpen_Ioo.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.mpr
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have hInt : (∫ x in (0 : ℝ)..1, f x) ≤ (b - a) + 2 * δ := by
    have := integral_le_of_support_subset (f := fun x => f x) f.continuous
      (fun x => (hfmem x).1) (fun x => (hfmem x).2) (p := a - δ) (q := b + δ)
      (by linarith) (fun x hx => hf0 hx)
    linarith [this]
  have hev : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Finset.range N, f (u n)) / N < (∫ x in (0 : ℝ)..1, f x) + δ :=
    Filter.Tendsto.eventually_lt_const (by linarith) (hequi (fun x => f x) f.continuous)
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hN0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hcount : (configCount u (Ico a b) N : ℝ) ≤ ∑ n ∈ Finset.range N, f (u n) :=
    configCount_le_sum u _ N _ (fun x => (hfmem x).1)
      (fun x hx => by
        have h := hf1 (Ico_subset_Icc_self hx)
        simp only [Pi.one_apply] at h
        simp [h])
  have : (configCount u (Ico a b) N : ℝ) / N ≤ (∑ n ∈ Finset.range N, f (u n)) / N := by
    gcongr
  linarith [hN, this]

/-- Eventually, the configuration density for `[a, b)` is bounded below by `b - a - 3δ`. -/
