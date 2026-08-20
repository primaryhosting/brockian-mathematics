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

lemma configCount_eq_mul (q r s N : ℕ) :
    configCount q r s N = residueCount q r N * residueCount q s N := by
  classical
  rw [configCount, residueCount, residueCount,
    Finset.filter_product (fun a : ℕ => a % q = r % q) (fun b : ℕ => b % q = s % q),
    Finset.card_product]

/-- Two-sided integral bounds for the residue count: `N - r % q ≤ q · count < N - r % q + q`. -/
