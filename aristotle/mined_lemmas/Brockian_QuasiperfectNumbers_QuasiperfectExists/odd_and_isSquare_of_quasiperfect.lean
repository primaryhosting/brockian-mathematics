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
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quasiperfect numbers

A natural number `n` is *quasiperfect* if `σ(n) = 2n + 1`, i.e. the sum of its proper
divisors is `n + 1`.  No quasiperfect number is known, and their existence is a
long-standing open problem.

This file proves Cattaneo's theorem — every quasiperfect number is an odd perfect
square — and deduces from it the conditional reduction
`Brockian.QuasiperfectNumbers.QuasiperfectExists`: a quasiperfect number exists if and
only if a quasiperfect number that is an odd perfect square exists.
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- `sigmaSum n` is the sum of all positive divisors of `n`. -/

theorem odd_and_isSquare_of_quasiperfect {n : ℕ} (h : Quasiperfect n) :
    Odd n ∧ IsSquare n := by
  obtain ⟨hn, heq⟩ := h
  have hn0 : n ≠ 0 := hn.ne'
  set a := n.factorization 2
  set x := n / 2 ^ a
  have hsplit : 2 ^ a * x = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hx0 : 0 < x := Nat.ordCompl_pos 2 hn0
  have hxodd : Odd x := by
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    exact Nat.not_dvd_ordCompl Nat.prime_two hn0
  have hcop : Nat.Coprime (2 ^ a) x :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl Nat.prime_two hn0)
  obtain ⟨N, hN, hNpos⟩ : ∃ N, 2 ^ (a + 1) = N ∧ 1 ≤ N :=
    ⟨2 ^ (a + 1), rfl, Nat.one_le_two_pow⟩
  -- the fundamental equation `σ(2^a) * σ(x) = 2n + 1`
  have key : (N - 1) * sigmaSum x = N * x + 1 := by
    have h1 := sigmaSum_mul_of_coprime hcop
    rw [hsplit, heq, sigmaSum_two_pow, hN, ← hsplit] at h1
    rw [← h1, ← hN]
    ring
  -- `σ(x)` is odd, hence `x` is a perfect square
  have hSodd : Odd (sigmaSum x) :=
    Nat.Odd.of_mul_right (m := N - 1) ⟨2 ^ a * x, by rw [key, ← hN]; ring⟩
  obtain ⟨y, hy⟩ : IsSquare x := isSquare_of_odd_of_sigmaSum_odd hxodd hSodd
  -- the exponent of `2` in `n` is zero
  have ha0 : a = 0 := by
    by_contra hane
    have h4 : (4 : ℕ) ∣ N := by
      rw [← hN]
      have h2 : (2 : ℕ) ^ 2 ∣ 2 ^ (a + 1) := pow_dvd_pow 2 (by omega)
      simpa using h2
    obtain ⟨c, hc⟩ := h4
    have hT4 : (N - 1) % 4 = 3 := by omega
    -- `N - 1` divides `x + 1`
    have hxS : x ≤ sigmaSum x := self_le_sigmaSum hx0
    obtain ⟨u, hu⟩ : ∃ u, sigmaSum x = x + u := ⟨sigmaSum x - x, by omega⟩
    have h2 : ((N - 1) * (x + u) : ℕ) = (N * x + 1 : ℕ) := by rw [← hu]; exact key
    have h3 : (((N - 1) * (x + u) : ℕ) : ℤ) = ((N * x + 1 : ℕ) : ℤ) := by exact_mod_cast h2
    rw [Nat.cast_mul, Nat.cast_sub hNpos] at h3
    push_cast at h3
    have hTu : (((N - 1) * u : ℕ) : ℤ) = ((x + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub hNpos]
      push_cast
      linarith
    have hTu' : (N - 1) * u = x + 1 := by exact_mod_cast hTu
    obtain ⟨p, hp, hp3, hpd⟩ := exists_prime_three_mod_four_dvd (N - 1) hT4
    refine not_dvd_sq_add_one (y := y) hp hp3 ?_
    have hpx : p ∣ x + 1 := hTu' ▸ hpd.mul_right u
    rwa [hy, ← sq] at hpx
  have hnx : n = x := by rw [← hsplit, ha0, pow_zero, one_mul]
  refine ⟨by rwa [hnx], ?_⟩
  rw [hnx, hy]
  exact ⟨y, rfl⟩

