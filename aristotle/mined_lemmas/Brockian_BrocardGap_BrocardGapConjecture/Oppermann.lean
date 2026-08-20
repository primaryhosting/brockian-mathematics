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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

/-- The number of primes strictly between `a` and `b`. -/

def Oppermann : Prop :=
  ∀ x : ℕ, 1 < x →
    (∃ p : ℕ, p.Prime ∧ x * x - x < p ∧ p < x * x) ∧
    (∃ p : ℕ, p.Prime ∧ x * x < p ∧ p < x * x + x)

/-- Under Oppermann's conjecture, for any `P ≥ 3` and any `q ≥ P + 2` there are at least
four primes strictly between `P²` and `q²`. -/
