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

theorem not_isUnitaryPerfect_prime_pow {p k : ℕ} (hp : p.Prime) :
    ¬ IsUnitaryPerfect (p ^ k) := by
  rintro ⟨hpos, heq⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp at heq
  · rw [usigma_prime_pow hp hk.ne'] at heq
    have h2 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
    omega

/-- A unitary perfect number has at least two distinct prime factors. -/
