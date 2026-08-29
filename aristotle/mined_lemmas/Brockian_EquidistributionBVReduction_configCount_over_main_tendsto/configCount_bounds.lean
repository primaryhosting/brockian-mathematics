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

lemma configCount_bounds (q r N : ℕ) (hq : 0 < q) :
    N * (N / q) ≤ configCount q r N ∧ configCount q r N ≤ N * (N / q) + N := by
  rw [configCount_eq_sum q r N hq]
  constructor
  · calc N * (N / q) = ∑ _a ∈ Finset.range N, N / q := by simp
    _ ≤ _ := Finset.sum_le_sum (fun a _ => Nat.le_add_right _ _)
  · calc ∑ a ∈ Finset.range N, (N / q + (if (r + (q - 1) * a) % q < N % q then 1 else 0))
        ≤ ∑ _a ∈ Finset.range N, (N / q + 1) :=
        Finset.sum_le_sum (fun a _ => by split <;> omega)
    _ = N * (N / q) + N := by simp [Nat.mul_add]

/-- Two-sided bound for the ratio `configCount / mainTerm`. -/
