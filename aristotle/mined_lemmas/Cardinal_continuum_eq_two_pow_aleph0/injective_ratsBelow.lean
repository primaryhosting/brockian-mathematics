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
# Continuum Eq Two Pow Aleph 0
Category: Frontier Wave 2 (deeper machinery)
Target: Cardinal.continuum_eq_two_pow_aleph0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Cardinal

/-- The cardinality of the continuum equals `2 ^ ℵ₀`.

In Mathlib `Cardinal.continuum` is *defined* as `2 ^ ℵ₀`, so this is the
identity witnessed by `Cardinal.two_power_aleph0`. -/

theorem injective_ratsBelow :
    Function.Injective (fun r : ℝ => {q : ℚ | (q : ℝ) < r}) := by
  intro r s hrs
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    have hq := Set.ext_iff.mp hrs q
    simp only [Set.mem_setOf_eq] at hq
    exact absurd (hq.mpr hq2) (not_lt.mpr hq1.le)
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
    have hq := Set.ext_iff.mp hrs q
    simp only [Set.mem_setOf_eq] at hq
    exact absurd (hq.mp hq2) (not_lt.mpr hq1.le)

/-- Upper bound: `#ℝ ≤ 2 ^ ℵ₀`, via the Dedekind-cut embedding `ℝ ↪ Set ℚ`. -/
