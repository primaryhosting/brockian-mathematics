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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite number `n > 1` such that every prime `p` dividing `n`
satisfies `p ∣ n / p - 1`. -/

lemma dvd_div_of_ne {n p q : ℕ} (hp : p ∈ n.primeFactors) (hq : q ∈ n.primeFactors)
    (hne : q ≠ p) : q ∣ n / p := by
  obtain ⟨hpp, hpd, hn0⟩ := Nat.mem_primeFactors.1 hp
  obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.1 hq
  obtain ⟨k, hk⟩ := hpd
  have hnp : n / p = k := by rw [hk, Nat.mul_div_cancel_left _ hpp.pos]
  rw [hnp]
  rcases (Nat.Prime.dvd_mul hqp).1 (hk ▸ hqd) with hd | hd
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp hpp).1 hd) hne
  · exact hd

/-- The key congruence: for a Giuga number `n`, we have `∑_{p ∣ n} n / p ≡ 1 (mod n)`. -/
