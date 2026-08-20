/-
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of "configurations" of size `N` at modulus `q`: ordered pairs `(a, b)` with
`a, b < N` and `a ≡ b [MOD q]`. -/

lemma abs_configCount_sub_main_le (q N : ℕ) (hq : 0 < q) :
    |(configCount q N : ℝ) - (N : ℝ) ^ 2 / (q : ℝ)| ≤ (N : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  set D : ℝ := ((N / q : ℕ) : ℝ) with hD
  have hDnn : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hdiv1 : (q : ℝ) * D ≤ (N : ℝ) := by
    rw [hD]; exact_mod_cast Nat.mul_div_le N q
  have hdiv2 : (N : ℝ) < (q : ℝ) * (D + 1) := by
    have h := Nat.lt_mul_div_succ N hq
    rw [hD]
    exact_mod_cast h
  have hup : (configCount q N : ℝ) ≤ (N : ℝ) * (D + 1) := by
    have h : ((configCount q N : ℕ) : ℝ) ≤ ((N * (N / q + 1) : ℕ) : ℝ) := by
      exact_mod_cast configCount_le q N
    rw [hD]
    push_cast at h ⊢
    linarith
  have hlo : (N : ℝ) * D ≤ (configCount q N : ℝ) := by
    have h : ((N * (N / q) : ℕ) : ℝ) ≤ ((configCount q N : ℕ) : ℝ) := by
      exact_mod_cast le_configCount q N hq
    rw [hD]
    push_cast at h ⊢
    linarith
  rw [abs_le]
  constructor
  · have h : (N : ℝ) ^ 2 / (q : ℝ) ≤ (N : ℝ) * D + (N : ℝ) := by
      rw [div_le_iff₀ hq0]
      nlinarith
    linarith
  · have h : (N : ℝ) * D ≤ (N : ℝ) ^ 2 / (q : ℝ) := by
      rw [le_div_iff₀ hq0]
      nlinarith
    linarith

/-- **Main result.** For a fixed modulus `q > 0`, the number of configurations of size `N`
divided by the main term `N ^ 2 / q` tends to `1` as `N → ∞`. -/
