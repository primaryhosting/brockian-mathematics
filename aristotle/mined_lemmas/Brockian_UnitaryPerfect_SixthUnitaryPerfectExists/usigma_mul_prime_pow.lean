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

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d` of `n` with `gcd d (n / d) = 1`. -/

lemma usigma_mul_prime_pow {m p k : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hk : k ≠ 0)
    (h : Nat.Coprime (p ^ k) m) : usigma (p ^ k * m) = (p ^ k + 1) * usigma m := by
  rw [usigma_mul_of_coprime (pow_ne_zero _ hp.pos.ne') hm h, usigma_prime_pow hp hk]

/-- One step of the computation of `σ*` from a prime factorization. -/
