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
# Woodall Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.WoodallPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian
namespace CullenWoodall

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/

theorem odd_prime_dvd_woodall (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (N : ℕ) :
    ∃ n, N < n ∧ p ∣ woodall n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hodd)
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  set m := (p + 1) / 2 with hm
  have h2m : 2 * m = p + 1 := by omega
  set t := m + p * N with ht
  set n := q * t + 1 with hn
  have hNn : N < n := by
    have e1 : N ≤ p * N := Nat.le_mul_of_pos_left N (by omega)
    have e3 : t ≤ q * t := Nat.le_mul_of_pos_left t (by omega)
    omega
  refine ⟨n, hNn, ?_⟩
  rw [dvd_woodall_iff (by omega)]
  have hpz : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hfer : ((2 : ZMod p)) ^ q = 1 := by
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    have h3 := ZMod.pow_card_sub_one_eq_one (p := p) (a := ((2 : ℕ) : ZMod p)) h2
    have hq1 : p - 1 = q := by omega
    rw [hq1] at h3
    simpa using h3
  have hpow : (2 : ZMod p) ^ n = 2 := by
    rw [hn, pow_succ, pow_mul, hfer, one_pow, one_mul]
  rw [hpow]
  have hqz : ((q : ℕ) : ZMod p) = -1 := by
    have h : ((p : ℕ) : ZMod p) = ((q + 1 : ℕ) : ZMod p) := by rw [← hq]
    rw [hpz] at h
    push_cast at h
    linear_combination -h
  have htz : ((t : ℕ) : ZMod p) = ((m : ℕ) : ZMod p) := by
    rw [ht]
    push_cast [hpz]
    ring
  have hnz : ((n : ℕ) : ZMod p) = 1 - ((m : ℕ) : ZMod p) := by
    rw [hn]
    push_cast [hqz, htz]
    ring
  have hmz : 2 * ((m : ℕ) : ZMod p) = 1 := by
    have h : ((2 * m : ℕ) : ZMod p) = ((p + 1 : ℕ) : ZMod p) := by rw [h2m]
    push_cast at h
    rw [hpz] at h
    linear_combination h
  rw [hnz]
  linear_combination -hmz

/-! ## Main conditional theorem -/

/-- **Woodall prime infinitude (conditional).**  The infinitude of the set of Woodall primes
follows from the (open) statement that Woodall primes occur with arbitrarily large index.
This is a genuine reduction: from unboundedness of the *index* set one obtains infinitude of
the set of *primes* of the form `n * 2 ^ n - 1`, using strict monotonicity of the Woodall
numbers. -/
