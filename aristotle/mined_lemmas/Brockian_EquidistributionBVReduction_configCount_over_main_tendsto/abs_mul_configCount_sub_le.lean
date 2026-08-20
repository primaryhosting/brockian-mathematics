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
