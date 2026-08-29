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

set_option maxRecDepth 8000

open Finset

namespace Brockian.UnitaryPerfect

/-! ## Unitary divisors and the unitary divisor sum -/

/-- The unitary divisors of `n`: the divisors `d` of `n` with `d` coprime to `n / d`. -/

theorem usigma_mul_prime {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hcop : Nat.Coprime m p) :
    usigma (m * p) = usigma m * (p + 1) := by
  rw [usigma_mul_of_coprime hm hp.pos.ne' hcop, usigma_prime hp]

/-! ## The five known unitary perfect numbers -/

