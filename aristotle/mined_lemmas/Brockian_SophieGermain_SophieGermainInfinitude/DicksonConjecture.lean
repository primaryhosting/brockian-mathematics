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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime: both `p` and `2 * p + 1` are prime. -/

def DicksonConjecture : Prop :=
  ∀ (k : ℕ) (a b : Fin k → ℤ), (∀ i, 0 < b i) →
    (∀ q : ℕ, q.Prime → ∃ n : ℤ, ¬ ((q : ℤ) ∣ ∏ i, (a i + b i * n))) →
    ∀ N : ℤ, ∃ n : ℤ, N < n ∧ ∀ i, Prime (a i + b i * n)

/-- The pair of linear forms `x` and `1 + 2 * x` is admissible: at `x = -1` the product of
the two forms equals `1`, hence is divisible by no prime. -/
