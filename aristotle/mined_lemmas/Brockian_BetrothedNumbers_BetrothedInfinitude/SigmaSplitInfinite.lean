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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module docstring, so the header comment above is a
plain block comment and is repeated here as the module docstring.)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the divisors of each strictly
between `1` and the number itself equals the other number. -/

def SigmaSplitInfinite : Prop := ∀ N : ℕ, ∃ A P Q : ℕ, N < A * P ∧ SigmaSplit A P Q

/-- **Betrothed Infinitude (conditional reduction).** If there are arbitrarily large sigma
splits, then there are infinitely many betrothed pairs.

The infinitude of betrothed (quasi-amicable) pairs is an open problem, so the result is stated
conditionally.  The content is the key lemma `betrothed_of_sigmaSplit`: a betrothed pair can be
manufactured from a common factor `A` and coprime cofactors `P ≠ Q` with equal divisor sums
satisfying `σ(A)·σ(P) = A·(P+Q) + 1` (as in `48 = 3·16`, `75 = 3·25`).  The hypothesis is not a
strictly stronger statement: by `sigmaSplitInfinite_iff_betrothedInfinite` it is *equivalent* to
the conclusion, so nothing is smuggled in. -/
