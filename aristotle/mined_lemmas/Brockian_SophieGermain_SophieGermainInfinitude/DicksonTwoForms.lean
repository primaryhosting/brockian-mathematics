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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-!`, so the header above
-- is reproduced verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

def DicksonTwoForms : Prop :=
  ∀ a b c d : ℕ, 0 < a → 0 < c →
    (∀ q : ℕ, q.Prime → ∃ n : ℕ, ¬ q ∣ (a * n + b) * (c * n + d)) →
    {n : ℕ | Nat.Prime (a * n + b) ∧ Nat.Prime (c * n + d)}.Infinite

/-- The pair of forms `n`, `2n + 1` relevant to Sophie Germain primes is admissible: no prime
divides `n * (2 * n + 1)` for every `n`. -/
