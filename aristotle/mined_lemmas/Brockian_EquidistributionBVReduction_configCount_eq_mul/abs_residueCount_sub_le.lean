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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

open Filter Finset

namespace Brockian.EquidistributionBVReduction

/-- The number of `n < N` lying in the residue class `r` modulo `q`. -/

lemma abs_residueCount_sub_le (q r N : ℕ) (hq : 0 < q) :
    |(residueCount q r N : ℝ) - (N : ℝ) / q| ≤ 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨hA, hB⟩ := residueCount_bounds q r N hq
  have hA' : (N : ℝ) - ((r % q : ℕ) : ℝ) ≤ (q : ℝ) * (residueCount q r N : ℝ) := by
    exact_mod_cast hA
  have hB' : (q : ℝ) * (residueCount q r N : ℝ) ≤ (N : ℝ) - ((r % q : ℕ) : ℝ) + (q : ℝ) := by
    exact_mod_cast hB.le
  have hrq : ((r % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast Nat.mod_lt _ hq
  have hrq0 : (0 : ℝ) ≤ ((r % q : ℕ) : ℝ) := by positivity
  have hNq : (N : ℝ) / q * (q : ℝ) = (N : ℝ) := by field_simp
  rw [abs_le]
  constructor <;> nlinarith [hq0, hA', hB', hrq, hrq0, hNq]

/-- Each residue class contains `(N / q) · (1 + o(1))` integers below `N`. -/
