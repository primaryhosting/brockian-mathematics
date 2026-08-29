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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The infinitude of Cullen primes (primes of the form `n * 2 ^ n + 1`) is an open
problem.  This file gives a Lean-checked *conditional reduction*: the infinitude of
Cullen primes follows from the existence of arbitrarily large odd `n` admitting a
Proth witness, i.e. an `a` with `a ^ ((n * 2 ^ n) / 2) = -1` modulo `n * 2 ^ n + 1`.
This is exactly the criterion (Proth's theorem, proved here from scratch) that is
used in practice to certify Cullen primes, and for odd `n` the condition is in fact
*equivalent* to primality of the Cullen number.

The file also contains unconditional results in the opposite direction: every odd
prime `p` divides the Cullen number `cullen (p - 2)`, hence infinitely many Cullen
numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/

theorem dvd_cullen_sub_two {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ cullen (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hodd)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdd
      exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdd)
    simpa using this
  have hfl : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  rw [← ZMod.natCast_eq_zero_iff]
  have hcast : ((cullen (p - 2) : ℕ) : ZMod p) = (-2) * (2 : ZMod p) ^ (p - 2) + 1 := by
    simp only [cullen, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one,
      Nat.cast_ofNat]
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hcast]
  have hstep : (2 : ZMod p) * ((-2) * (2 : ZMod p) ^ (p - 2) + 1) = 0 := by
    have hexp : (2 : ZMod p) ^ (p - 2) * 2 = (2 : ZMod p) ^ (p - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    calc (2 : ZMod p) * ((-2) * (2 : ZMod p) ^ (p - 2) + 1)
        = -2 * ((2 : ZMod p) ^ (p - 2) * 2) + 2 := by ring
      _ = -2 * (1 : ZMod p) + 2 := by rw [hexp, hfl]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hstep with h | h
  · exact absurd h h2ne
  · exact h

/-- Unconditional: infinitely many Cullen numbers are composite. -/
