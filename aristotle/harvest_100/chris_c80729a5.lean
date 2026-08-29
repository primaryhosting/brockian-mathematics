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

open scoped BigOperators
open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The *total* count: the number of natural numbers `n < N` that lie in the
residue class `a` modulo `q`. -/
def totalCount (q a N : ℕ) : ℕ := N.count (fun n => n ≡ a [MOD q])

/-- The *main term* predicted by equidistribution: a residue class mod `q` should
contain roughly a proportion `1 / q` of the integers below `N`. -/
noncomputable def mainTerm (q N : ℕ) : ℝ := (N : ℝ) / (q : ℝ)

/-- Exact evaluation of the total count as a ceiling, from `Nat.count_modEq_card_eq_ceil`. -/
lemma totalCount_eq_ceil (q a N : ℕ) (hq : 0 < q) :
    ((totalCount q a N : ℤ)) = ⌈((N : ℚ) - ((a % q : ℕ) : ℚ)) / (q : ℚ)⌉ :=
  Nat.count_modEq_card_eq_ceil N hq a

/-- The total count differs from the main term by at most `1`: two-sided integer bounds. -/
lemma totalCount_bounds (q a N : ℕ) (hq : 0 < q) :
    (N : ℤ) ≤ (q : ℤ) * (totalCount q a N : ℤ) + (q : ℤ) ∧
      (q : ℤ) * (totalCount q a N : ℤ) ≤ (N : ℤ) + (q : ℤ) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  set c : ℤ := (totalCount q a N : ℤ) with hc
  set x : ℚ := ((N : ℚ) - ((a % q : ℕ) : ℚ)) / (q : ℚ) with hx
  have hceil : c = ⌈x⌉ := totalCount_eq_ceil q a N hq
  -- lower bound from `x ≤ ⌈x⌉`
  have h1 : (N : ℚ) - ((a % q : ℕ) : ℚ) ≤ (q : ℚ) * (c : ℚ) := by
    have hle : x ≤ (c : ℚ) := by
      rw [hceil]; exact_mod_cast Int.le_ceil x
    rw [hx, div_le_iff₀ hq'] at hle
    linarith
  -- upper bound from `⌈x⌉ < x + 1`
  have h2 : (q : ℚ) * (c : ℚ) < (N : ℚ) - ((a % q : ℕ) : ℚ) + (q : ℚ) := by
    have hlt0 : (c : ℚ) < x + 1 := by
      rw [hceil]; exact_mod_cast Int.ceil_lt_add_one x
    have hlt : (q : ℚ) * (c : ℚ) < (q : ℚ) * (x + 1) := mul_lt_mul_of_pos_left hlt0 hq'
    have hqx : (q : ℚ) * x = (N : ℚ) - ((a % q : ℕ) : ℚ) := by
      rw [hx]; field_simp
    nlinarith [hqx]
  have h1' : (N : ℤ) - ((a % q : ℕ) : ℤ) ≤ (q : ℤ) * c := by exact_mod_cast h1
  have h2' : (q : ℤ) * c < (N : ℤ) - ((a % q : ℕ) : ℤ) + (q : ℤ) := by exact_mod_cast h2
  have h3 : ((a % q : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast Nat.mod_lt a hq
  have h4 : (0 : ℤ) ≤ ((a % q : ℕ) : ℤ) := Int.natCast_nonneg _
  exact ⟨by linarith, by linarith⟩

/-- Real-valued form of the two-sided bound. -/
lemma abs_mul_totalCount_sub_le (q a N : ℕ) (hq : 0 < q) :
    |(q : ℝ) * (totalCount q a N : ℝ) - (N : ℝ)| ≤ (q : ℝ) := by
  obtain ⟨hA, hB⟩ := totalCount_bounds q a N hq
  have hA' : (N : ℝ) ≤ (q : ℝ) * (totalCount q a N : ℝ) + (q : ℝ) := by exact_mod_cast hA
  have hB' : (q : ℝ) * (totalCount q a N : ℝ) ≤ (N : ℝ) + (q : ℝ) := by exact_mod_cast hB
  rw [abs_le]
  constructor <;> linarith

/-- **Equidistribution in a residue class**: the total count over the main term tends to `1`.

This discharges the named hypothesis `total_over_main_tendsto`, making it unconditional. -/
theorem total_over_main_tendsto (q a : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (totalCount q a N : ℝ) / mainTerm q N) atTop (𝓝 1) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have key : Tendsto (fun N : ℕ => (totalCount q a N : ℝ) / mainTerm q N - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (q : ℝ))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hrw : (totalCount q a N : ℝ) / mainTerm q N - 1
        = ((q : ℝ) * (totalCount q a N : ℝ) - (N : ℝ)) / (N : ℝ) := by
      rw [mainTerm]
      field_simp
    rw [Real.norm_eq_abs, hrw, abs_div, abs_of_pos hNpos]
    gcongr
    exact abs_mul_totalCount_sub_le q a N hq
  have h := key.add_const 1
  simpa using h

end Brockian.EquidistributionBVReduction

