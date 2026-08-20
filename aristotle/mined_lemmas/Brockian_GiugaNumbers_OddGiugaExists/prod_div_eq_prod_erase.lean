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

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite natural number `n > 1` such that
`p ∣ n / p - 1` for every prime `p` dividing `n`. -/

theorem prod_div_eq_prod_erase {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) (p : ℕ) (hpS : p ∈ S) :
    (∏ q ∈ S, q) / p = ∏ q ∈ S.erase p, q := by
  classical
  have h : p * ∏ q ∈ S.erase p, q = ∏ q ∈ S, q := Finset.mul_prod_erase S (fun q => q) hpS
  rw [← h, Nat.mul_div_cancel_left _ (hp p hpS).pos]

/-- Key arithmetic lemma: if `S` is a set of at least two primes such that each `p ∈ S`
divides `(∏ q ∈ S.erase p, q) - 1`, then the sum of the reciprocals of the elements of `S`
exceeds `1`. -/
