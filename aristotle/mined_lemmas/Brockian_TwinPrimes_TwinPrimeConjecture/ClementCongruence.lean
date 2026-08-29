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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The twin prime conjecture itself is open, so what is proved here is a
*Lean-checked reduction*: the twin prime conjecture is shown to be equivalent to
an explicit elementary congruence condition (Clement's criterion), together with
some unconditional partial results.
-/

namespace Brockian.TwinPrimes

open Nat

/-- `n` is the smaller member of a twin prime pair. -/

def ClementCongruence (n : ℕ) : Prop := n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n

/-! ### Wilson's theorem in divisibility form -/

/-- Wilson's theorem, stated as a divisibility criterion for primality. -/
