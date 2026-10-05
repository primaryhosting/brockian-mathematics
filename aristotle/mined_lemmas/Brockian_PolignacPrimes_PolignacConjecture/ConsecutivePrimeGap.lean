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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- comment above appears directly after the import.)

namespace Brockian.PolignacPrimes

open Finset

/-- `ConsecutivePrimeGap n p` says that `p` and `p + n` are primes and that there is no
prime strictly between them, i.e. `p` and `p + n` are *consecutive* primes with gap `n`. -/

def ConsecutivePrimeGap (n p : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime (p + n) ∧ ∀ q, p < q → q < p + n → ¬ Nat.Prime q

/-- The two-form Dickson (prime-tuples) hypothesis: for an arithmetic progression `a * x + b`
with `a > 0`, if the pair of linear forms `a * x + b`, `a * x + b + c` is admissible — i.e. for
every prime `Q` there is some `x` for which `Q` divides neither value — then both forms are
simultaneously prime for infinitely many `x`. -/
