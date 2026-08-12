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

/-
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the sequence value `x n` lies in `[0, a)`,
viewed as a real number.  This is the *total* count appearing in the bounded–variation
reduction step of an equidistribution argument. -/
noncomputable def count (x : ℕ → ℝ) (a : ℝ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter fun n => x n ∈ Set.Ico (0 : ℝ) a).card : ℝ)

/-- The *main term* `N * a`: the count one expects from an equidistributed sequence. -/
noncomputable def mainTerm (a : ℝ) (N : ℕ) : ℝ := (N : ℝ) * a

/-- Abstract form of the statement: if a quantity `total` differs from a nonzero scale factor
by an error that is negligible after rescaling, then the ratio `total / main` tends to `1`.

Here `f N = total N / N` is the normalized count and `a` is the expected density. -/
theorem ratio_tendsto_one_of_sub_tendsto_zero
    {f : ℕ → ℝ} {a : ℝ} (ha : a ≠ 0)
    (h : Tendsto (fun N => f N - a) atTop (𝓝 0)) :
    Tendsto (fun N => f N / a) atTop (𝓝 1) := by
  have hf : Tendsto f atTop (𝓝 a) := by
    have := h.add (tendsto_const_nhds (x := a) (f := (atTop : Filter ℕ)))
    simpa using this
  have := hf.div_const a
  rwa [div_self ha] at this

/-- **Total over main tends to one.**

If the normalized counting function `count x a N / N` of the sequence `x` converges to the
density `a` of the interval `[0, a)` (the equidistribution hypothesis, which in the
bounded–variation reduction is supplied by the discrepancy estimate), then the ratio of the
total count to the main term `N * a` tends to `1`.

Previously this was assumed as a named hypothesis; it is now unconditional given the
equidistribution input. -/
theorem total_over_main_tendsto
    (x : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hdisc : Tendsto (fun N => count x a N / (N : ℝ) - a) atTop (𝓝 0)) :
    Tendsto (fun N => count x a N / mainTerm a N) atTop (𝓝 1) := by
  have key := ratio_tendsto_one_of_sub_tendsto_zero (f := fun N => count x a N / (N : ℝ))
    ha.ne' hdisc
  refine key.congr fun N => ?_
  simp [mainTerm, div_div]

/-- The (one-sided, interval `[0,a)`) discrepancy of the first `N` terms of `x`. -/
noncomputable def discrepancy (x : ℕ → ℝ) (a : ℝ) (N : ℕ) : ℝ :=
  |count x a N / (N : ℝ) - a|

/-- A discrepancy bound tending to zero suffices: this is the form in which the
bounded-variation reduction supplies the hypothesis of `total_over_main_tendsto`. -/
theorem total_over_main_tendsto_of_discrepancy
    (x : ℕ → ℝ) (a : ℝ) (ha : 0 < a) {D : ℕ → ℝ}
    (hbound : ∀ᶠ N in atTop, discrepancy x a N ≤ D N)
    (hD : Tendsto D atTop (𝓝 0)) :
    Tendsto (fun N => count x a N / mainTerm a N) atTop (𝓝 1) := by
  refine total_over_main_tendsto x a ha ?_
  refine squeeze_zero_norm' ?_ hD
  filter_upwards [hbound] with N hN
  simpa [discrepancy, Real.norm_eq_abs] using hN

/-- The count never exceeds the number of terms considered. -/
theorem count_le (x : ℕ → ℝ) (a : ℝ) (N : ℕ) : count x a N ≤ (N : ℝ) := by
  have h := Finset.card_filter_le (Finset.range N) fun n => x n ∈ Set.Ico (0 : ℝ) a
  have := (Nat.cast_le (α := ℝ)).2 h
  simpa [count] using this

/-- The count is nonnegative. -/
theorem count_nonneg (x : ℕ → ℝ) (a : ℝ) (N : ℕ) : 0 ≤ count x a N := by
  unfold count; positivity

section Nonvacuous

/-- For the constant zero sequence and `a = 1`, every term is counted. -/
theorem count_zero_one (N : ℕ) : count (fun _ => (0 : ℝ)) 1 N = (N : ℝ) := by
  simp [count]

/-- The hypothesis of `total_over_main_tendsto` is satisfiable: the constant zero sequence
has vanishing discrepancy for the interval `[0, 1)`. -/
theorem discrepancy_zero_one_tendsto :
    Tendsto (fun N => count (fun _ => (0 : ℝ)) 1 N / (N : ℝ) - 1) atTop (𝓝 0) := by
  have h : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
      fun N => count (fun _ => (0 : ℝ)) 1 N / (N : ℝ) - 1 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [count_zero_one, div_self hN', sub_self]
  exact tendsto_const_nhds.congr' h

/-- A concrete instance of `total_over_main_tendsto`, witnessing that the theorem is
not vacuously true. -/
theorem total_over_main_tendsto_zero_one :
    Tendsto (fun N => count (fun _ => (0 : ℝ)) 1 N / mainTerm 1 N) atTop (𝓝 1) :=
  total_over_main_tendsto _ 1 one_pos discrepancy_zero_one_tendsto

/-!
### A nontrivial equidistributed example

The two-periodic sequence `evenSeq n = if n even then 0 else 1/2` hits the interval
`[0, 1/2)` exactly at the even indices, so its counting function has discrepancy `O(1/N)`
for the density `a = 1/2`.  This gives an instance of `total_over_main_tendsto` with
`a ≠ 1`.
-/

/-- The two-periodic sequence taking the value `0` at even indices and `1/2` at odd ones. -/
noncomputable def evenSeq : ℕ → ℝ := fun n => if n % 2 = 0 then 0 else 1 / 2

/-- The number of even numbers below `N`. -/
theorem card_even_range (N : ℕ) :
    ((Finset.range N).filter (fun n => n % 2 = 0)).card = (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases h : n % 2 = 0
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), ih]
      omega
    · rw [if_neg h, ih]; omega

/-- The counting function of `evenSeq` for the interval `[0, 1/2)`. -/
theorem count_evenSeq (N : ℕ) : count evenSeq (1 / 2) N = (((N + 1) / 2 : ℕ) : ℝ) := by
  unfold count
  congr 1
  rw [← card_even_range N]
  congr 1
  apply Finset.filter_congr
  intro n _
  by_cases h : n % 2 = 0 <;> simp [evenSeq, h]

/-- The discrepancy of `evenSeq` for the interval `[0, 1/2)` is at most `1 / N`. -/
theorem discrepancy_evenSeq_le (N : ℕ) (hN : 0 < N) :
    discrepancy evenSeq (1 / 2) N ≤ 1 / (N : ℝ) := by
  rw [discrepancy, count_evenSeq]
  have h1 : 2 * ((N + 1) / 2) + (N + 1) % 2 = N + 1 := Nat.div_add_mod (N + 1) 2
  have h2 : (N + 1) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set c : ℝ := (((N + 1) / 2 : ℕ) : ℝ) with hc
  have h1' : 2 * c + (((N + 1) % 2 : ℕ) : ℝ) = (N : ℝ) + 1 := by
    have := congrArg (fun k : ℕ => (k : ℝ)) h1
    push_cast at this
    linarith [this]
  have h2' : (((N + 1) % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast h2
  have h3 : (0 : ℝ) ≤ (((N + 1) % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have key : c / (N : ℝ) - 1 / 2 = (2 * c - (N : ℝ)) / (2 * (N : ℝ)) := by field_simp
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (N : ℝ))]
  have habs : |2 * c - (N : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |2 * c - (N : ℝ)| / (2 * (N : ℝ)) ≤ 1 / (2 * (N : ℝ)) := by gcongr
    _ ≤ 1 / (N : ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) hNR
        linarith

/-- An instance of `total_over_main_tendsto` with density `a = 1/2`: for the two-periodic
sequence `evenSeq`, the total count over the main term `N / 2` tends to `1`. -/
theorem total_over_main_tendsto_evenSeq :
    Tendsto (fun N => count evenSeq (1 / 2) N / mainTerm (1 / 2) N) atTop (𝓝 1) := by
  refine total_over_main_tendsto_of_discrepancy evenSeq (1 / 2) (by norm_num)
    (D := fun N : ℕ => 1 / (N : ℝ)) ?_ tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact discrepancy_evenSeq_le N hN

end Nonvacuous

end EquidistributionBVReduction
end Brockian

