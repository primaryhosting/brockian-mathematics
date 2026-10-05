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
# Fermat Prime Beyond Four
Category: Brockian Conjecture
Target: Brockian.FermatNumbers.FermatPrimeBeyondFour
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.FermatNumbers

private instance factPrimeThree : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The Pépin condition for the `n`-th Fermat number `Fₙ = 2 ^ 2 ^ n + 1`:
`3 ^ ((Fₙ - 1) / 2) = -1` in `ZMod Fₙ`. -/

theorem prime_fermatNumber_iff_pepinCondition (n : ℕ) (hn : 1 ≤ n) :
    Nat.Prime (Nat.fermatNumber n) ↔ PepinCondition n :=
  ⟨pepinCondition_of_prime n hn, fun h => Nat.pepin_primality n h⟩

/-- **Reduction of the "Fermat prime beyond four" problem.**
There is a Fermat prime `Fₙ` with `n > 4` if and only if some `n > 4` passes Pépin's test.
(Whether either side holds is a famous open problem.) -/
