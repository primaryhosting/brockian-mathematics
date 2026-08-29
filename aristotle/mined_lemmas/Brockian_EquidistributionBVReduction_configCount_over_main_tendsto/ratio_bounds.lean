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

open scoped BigOperators
open Filter Finset

namespace Brockian.EquidistributionBVReduction

/-- The set of *configurations* of size `N` in the residue class `r` modulo `q`:
pairs `(a, b)` with `a, b < N` and `a + b ≡ r [MOD q]`. -/

lemma ratio_bounds (q r N : ℕ) (hq : 0 < q) (hN : 0 < N) :
    ((N : ℝ) - q) / N ≤ (configCount q r N : ℝ) / mainTerm q N ∧
      (configCount q r N : ℝ) / mainTerm q N ≤ ((N : ℝ) + q) / N := by
  obtain ⟨hlow, hhigh⟩ := configCount_bounds q r N hq
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hd1 : (q : ℝ) * ((N / q : ℕ) : ℝ) ≤ (N : ℝ) := by
    have : q * (N / q) ≤ N := Nat.mul_div_le N q
    exact_mod_cast this
  have hd2 : (N : ℝ) ≤ (q : ℝ) * ((N / q : ℕ) : ℝ) + q := by
    have : N ≤ q * (N / q) + q := by
      have h := Nat.div_add_mod N q
      have h2 : N % q < q := Nat.mod_lt _ hq
      omega
    exact_mod_cast this
  have hlowR : (N : ℝ) * ((N / q : ℕ) : ℝ) ≤ (configCount q r N : ℝ) := by exact_mod_cast hlow
  have hhighR : (configCount q r N : ℝ) ≤ (N : ℝ) * ((N / q : ℕ) : ℝ) + N := by exact_mod_cast hhigh
  have hratio :
      (configCount q r N : ℝ) / mainTerm q N = (configCount q r N : ℝ) * q / (N : ℝ) ^ 2 := by
    show (configCount q r N : ℝ) / ((N : ℝ) ^ 2 / q) = _
    field_simp
  rw [hratio]
  generalize ((N / q : ℕ) : ℝ) = d at hd1 hd2 hlowR hhighR
  generalize ((configCount q r N : ℕ) : ℝ) = C at hlowR hhighR ⊢
  have hsq : (0:ℝ) ≤ (N : ℝ) ^ 2 := sq_nonneg _
  have hqN : (0:ℝ) ≤ (q : ℝ) * N := by positivity
  constructor
  · rw [div_le_div_iff₀ hNR (by positivity)]
    have h3 : (N : ℝ) ^ 2 * N ≤ (N : ℝ) ^ 2 * ((q : ℝ) * d + q) := mul_le_mul_of_nonneg_left hd2 hsq
    have h4 : ((N : ℝ) * d) * ((q : ℝ) * N) ≤ C * ((q : ℝ) * N) :=
      mul_le_mul_of_nonneg_right hlowR hqN
    nlinarith [h3, h4]
  · rw [div_le_div_iff₀ (by positivity) hNR]
    have h3 : (N : ℝ) ^ 2 * ((q : ℝ) * d) ≤ (N : ℝ) ^ 2 * N := mul_le_mul_of_nonneg_left hd1 hsq
    have h4 : C * ((q : ℝ) * N) ≤ ((N : ℝ) * d + N) * ((q : ℝ) * N) :=
      mul_le_mul_of_nonneg_right hhighR hqN
    nlinarith [h3, h4]

/-- The lower comparison sequence `(N - q) / N` tends to `1`. -/
