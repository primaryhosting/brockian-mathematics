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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The number of "configurations" below `N` in the arithmetic progression
`a mod q`, i.e. the cardinality of `{n < N | n ≡ a [MOD q]}`. -/
def configCount (q a N : ℕ) : ℕ :=
  {n ∈ Finset.range N | n ≡ a [MOD q]}.card

/-- The expected main term for `configCount q a N`, namely `N / q`. -/
noncomputable def mainTerm (q N : ℕ) : ℝ := (N : ℝ) / (q : ℝ)

/-- Exact evaluation of `configCount`, from `Nat.count_modEq_card`. -/
theorem configCount_eq (q a N : ℕ) (hq : 0 < q) :
    configCount q a N = N / q + (if a % q < N % q then 1 else 0) := by
  have h : configCount q a N = Nat.count (fun x => x ≡ a [MOD q]) N := by
    rw [Nat.count_eq_card_filter_range]
    rfl
  rw [h, Nat.count_modEq_card N hq a]

/-- Two-sided bound: `q * configCount q a N` differs from `N` by at most `q`. -/
theorem abs_mul_configCount_sub_le (q a N : ℕ) (hq : 0 < q) :
    |(q : ℝ) * (configCount q a N : ℝ) - (N : ℝ)| ≤ (q : ℝ) := by
  have hdm : q * (N / q) + N % q = N := Nat.div_add_mod N q
  have hmod : N % q < q := Nat.mod_lt _ hq
  have hle : q * configCount q a N ≤ N + q ∧ N ≤ q * configCount q a N + q := by
    rw [configCount_eq q a N hq, Nat.mul_add]
    by_cases hc : a % q < N % q <;> simp [hc] <;> omega
  obtain ⟨h1, h2⟩ := hle
  have h1' : ((q * configCount q a N : ℕ) : ℝ) ≤ ((N + q : ℕ) : ℝ) := Nat.cast_le.2 h1
  have h2' : ((N : ℕ) : ℝ) ≤ ((q * configCount q a N + q : ℕ) : ℝ) := Nat.cast_le.2 h2
  push_cast at h1' h2'
  rw [abs_le]
  constructor <;> linarith

/-- **Equidistribution of an arithmetic progression, ratio form.**
The number of `n < N` with `n ≡ a [MOD q]`, divided by the main term `N / q`,
tends to `1` as `N → ∞`. -/
theorem configCount_over_main_tendsto (q a : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (configCount q a N : ℝ) / mainTerm q N) atTop (𝓝 1) := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- the error term `q / N` tends to `0`
  have herr : Tendsto (fun N : ℕ => (q : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (q : ℝ))
  rw [Metric.tendsto_atTop] at herr ⊢
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := herr ε hε
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right N₀ 1) hN
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hb := abs_mul_configCount_sub_le q a N hq
  have key : (configCount q a N : ℝ) / mainTerm q N - 1
      = ((q : ℝ) * (configCount q a N : ℝ) - (N : ℝ)) / (N : ℝ) := by
    rw [mainTerm, div_div_eq_mul_div]
    field_simp
  have hdist : dist ((configCount q a N : ℝ) / mainTerm q N) 1 ≤ (q : ℝ) / (N : ℝ) := by
    rw [Real.dist_eq, key, abs_div, abs_of_pos hNR]
    gcongr
  have h2 := hN₀ N (le_trans (le_max_left N₀ 1) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  linarith

end Brockian.EquidistributionBVReduction

