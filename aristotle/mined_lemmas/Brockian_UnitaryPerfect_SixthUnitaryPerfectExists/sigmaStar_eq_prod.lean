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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.UnitaryPerfect

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd (d, n / d) = 1`. -/

theorem sigmaStar_eq_prod {n : ℕ} (hn : n ≠ 0) :
    sigmaStar n = ∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p) := by
  rw [Nat.multiplicative_factorization sigmaStar (fun _ _ hxy => sigmaStar_mul_of_coprime hxy)
    sigmaStar_one hn, Finsupp.prod]
  refine Finset.prod_congr n.support_factorization fun p hp => ?_
  exact sigmaStar_prime_pow (Nat.prime_of_mem_primeFactors hp)
    (by simpa using (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hn
      (Nat.dvd_of_mem_primeFactors hp)).ne')

