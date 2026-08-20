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

lemma residueCount_bounds (q r N : ℕ) (hq : 0 < q) :
    (N : ℤ) - ((r % q : ℕ) : ℤ) ≤ (q : ℤ) * (residueCount q r N : ℤ) ∧
      (q : ℤ) * (residueCount q r N : ℤ) < (N : ℤ) - ((r % q : ℕ) : ℤ) + (q : ℤ) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hcount := Nat.count_modEq_card_eq_ceil (r := q) (b := N) hq r
  rw [Nat.count_eq_card_filter_range] at hcount
  have hfil : #{n ∈ Finset.range N | n ≡ r [MOD q]} = residueCount q r N := rfl
  rw [hfil] at hcount
  set c : ℕ := residueCount q r N with hc
  set x : ℚ := ((N : ℚ) - ((r % q : ℕ) : ℚ)) / (q : ℚ) with hx
  have hlow : x ≤ (c : ℚ) := by
    have h := Int.le_ceil x
    rw [← hcount] at h
    exact_mod_cast h
  have hhigh : (c : ℚ) < x + 1 := by
    have h := Int.ceil_lt_add_one x
    rw [← hcount] at h
    exact_mod_cast h
  rw [hx, div_le_iff₀ hq'] at hlow
  rw [hx, ← sub_lt_iff_lt_add, lt_div_iff₀ hq'] at hhigh
  constructor
  · have : ((N : ℚ) - ((r % q : ℕ) : ℚ)) ≤ (q : ℚ) * (c : ℚ) := by linarith
    exact_mod_cast this
  · have : (q : ℚ) * (c : ℚ) < (N : ℚ) - ((r % q : ℕ) : ℚ) + (q : ℚ) := by linarith
    exact_mod_cast this

/-- The residue count is within `1` of `N / q`. -/
