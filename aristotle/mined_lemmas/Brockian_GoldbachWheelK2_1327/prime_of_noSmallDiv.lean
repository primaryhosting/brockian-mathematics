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

namespace Brockian

/-! ## A kernel-friendly primality test

Mathlib's `Decidable` instance for `Nat.Prime` performs a linear scan, which makes
`by decide` unusable for numbers of the size we need.  We therefore set up a trial
division test by divisors `≤ 63`, which is sound for all `n < 64 ^ 2 = 4096`.
-/

/-- `noSmallDiv n k = true` asserts that no `d` with `2 ≤ d ≤ k` and `d ≠ n` divides `n`. -/

lemma prime_of_noSmallDiv {n k : ℕ} (h2 : 2 ≤ n) (hk : n < (k + 1) * (k + 1))
    (h : noSmallDiv n k = true) : Nat.Prime n := by
  by_contra hp
  have hpos : 0 < n := by omega
  have hsq : n.minFac * n.minFac ≤ n := by
    have := Nat.minFac_sq_le_self hpos hp
    nlinarith [this]
  have hmf2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hle : n.minFac ≤ k := by nlinarith
  have hne : n.minFac ≠ n := by nlinarith
  exact noSmallDiv_spec h hmf2 hle hne hdvd

/-- Boolean primality test; it is sound (`prime_of_isPrimeB`) for all `n < 4096`. -/
