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
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `d` is a *unitary divisor* of `n` if `d ∣ n` and `d` is coprime to `n / d`. -/

lemma prod_pow_coprime_prod_pow {n : ℕ} {S T : Finset ℕ} (hS : S ⊆ n.primeFactors)
    (hT : T ⊆ n.primeFactors) (hdisj : Disjoint S T) :
    Nat.Coprime (∏ p ∈ S, p ^ n.factorization p) (∏ p ∈ T, p ^ n.factorization p) := by
  refine Nat.Coprime.prod_left (fun p hp => Nat.Coprime.prod_right (fun q hq => ?_))
  have hpq : p ≠ q := by
    rintro rfl
    exact (Finset.disjoint_left.mp hdisj hp) hq
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hS hp))
    (Nat.prime_of_mem_primeFactors (hT hq))).mpr hpq)

/-- The unitary divisors of `n` are exactly the products `∏ p ∈ S, p ^ (n.factorization p)`
over subsets `S` of the prime factors of `n`. -/
