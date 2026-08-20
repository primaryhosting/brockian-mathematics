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

def SigmaSplit (A P Q : ℕ) : Prop :=
  0 < A ∧ 0 < P ∧ 0 < Q ∧ P ≠ Q ∧ Nat.Coprime A P ∧ Nat.Coprime A Q ∧
    sigma 1 P = sigma 1 Q ∧ sigma 1 A * sigma 1 P = A * (P + Q) + 1

/-- **Key lemma.** Every sigma split produces a betrothed pair. -/
