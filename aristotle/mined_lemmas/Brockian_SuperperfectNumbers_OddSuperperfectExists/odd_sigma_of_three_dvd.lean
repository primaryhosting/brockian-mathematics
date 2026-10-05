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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.SuperperfectNumbers

/-- A natural number `n` is *superperfect* if `σ (σ n) = 2 * n`, where `σ` is the
sum-of-divisors function. -/

theorem odd_sigma_of_three_dvd {n : ℕ} (hodd : Odd n) (h : Superperfect n) (h3 : 3 ∣ n) :
    Odd (σ 1 n) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  have hn1000 : 1000 < n := by
    by_contra hle
    exact no_odd_superperfect_le_1000 n (by omega) hodd h
  obtain ⟨j, hj⟩ := h3
  have hjdvd : j ∣ n := ⟨3, by omega⟩
  have h1 : n + j + 1 ≤ σ 1 n := add_add_one_le_sigma_of_dvd hjdvd (by omega) (by omega)
  obtain ⟨k, hk⟩ := hev
  have hkdvd : k ∣ σ 1 n := ⟨2, by omega⟩
  have h2 : σ 1 n + k + 1 ≤ σ 1 (σ 1 n) :=
    add_add_one_le_sigma_of_dvd hkdvd (by omega) (by omega)
  have h3 : σ 1 (σ 1 n) = 2 * n := h
  omega

/-- An odd superperfect number divisible by `3` is a perfect square. -/
