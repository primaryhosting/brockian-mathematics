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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem pow_lt_two_pow_d {n B t : ℕ} (hn : 2 ≤ n) (hB : n < 2 ^ B) (ht : 100 * B ^ 2 < t) :
    n ^ (2 * Nat.sqrt t) < 2 ^ (2 * (Nat.sqrt t + 1) * B) := by
  have hB1 : 1 ≤ B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · rw [h] at hB; simp at hB; omega
    · exact h
  have h1 : 10 * B ≤ Nat.sqrt t := sqrt_ge_of_lt ht
  calc n ^ (2 * Nat.sqrt t) < (2 ^ B) ^ (2 * Nat.sqrt t) :=
        Nat.pow_lt_pow_left hB (by omega)
    _ = 2 ^ (B * (2 * Nat.sqrt t)) := by rw [← pow_mul]
    _ ≤ 2 ^ (2 * (Nat.sqrt t + 1) * B) := Nat.pow_le_pow_right (by omega) (by ring_nf; omega)

end AKS

import Mathlib

/-!
# Introspective numbers

Following Agrawal–Kayal–Saxena, a natural number `m` is *introspective* for a polynomial
`f` (with respect to a modulus `r`) when

  `f(X)^m ≡ f(X^m)  (mod X^r - 1)`.

This file develops the basic closure properties: introspective numbers are closed under
multiplication, and for a fixed `m` the polynomials for which `m` is introspective are
closed under multiplication.
-/

namespace AKS

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `m` is introspective for `f` modulo `X ^ r - 1`. -/
