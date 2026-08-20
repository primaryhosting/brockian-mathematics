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
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A *Giuga number* is a composite natural number `n > 1` such that every prime `p`
dividing `n` satisfies `p ∣ n / p - 1`. -/

theorem div_eq_prod_erase {n : ℕ} (hsq : ∏ p ∈ n.primeFactors, p = n) {p : ℕ}
    (hp : p ∈ n.primeFactors) : n / p = ∏ r ∈ n.primeFactors.erase p, r := by
  have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  have hx : p * ∏ r ∈ n.primeFactors.erase p, r = n :=
    (Finset.mul_prod_erase _ (fun r => r) hp).trans hsq
  conv_lhs => rw [← hx]
  exact Nat.mul_div_cancel_left _ hp0

/-- The key arithmetic fact: for a Giuga number `n`, the sum of the reciprocals of its
prime divisors exceeds `1`. -/
