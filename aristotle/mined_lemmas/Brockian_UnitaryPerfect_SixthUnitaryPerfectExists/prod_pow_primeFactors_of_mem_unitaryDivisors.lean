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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: divisors `d` with `gcd (d, n / d) = 1`. -/

lemma prod_pow_primeFactors_of_mem_unitaryDivisors {n d : ℕ} (hd : d ∈ unitaryDivisors n) :
    (∏ p ∈ d.primeFactors, p ^ n.factorization p) = d := by
  calc (∏ p ∈ d.primeFactors, p ^ n.factorization p)
      = ∏ p ∈ d.primeFactors, p ^ d.factorization p :=
        Finset.prod_congr rfl fun p hp => by
          rw [factorization_eq_of_mem_unitaryDivisors hd hp]
    _ = d := prod_primeFactors_pow_factorization (ne_zero_of_mem_unitaryDivisors hd)

/-- The product formula `σ*(n) = ∏_{p ∣ n} (p^{v_p(n)} + 1)`. -/
