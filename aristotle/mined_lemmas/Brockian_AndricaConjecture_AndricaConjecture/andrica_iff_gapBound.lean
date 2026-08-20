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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian.AndricaConjecture

/-- `nthPrime n` is the `n`-th prime number (`nthPrime 0 = 2`, `nthPrime 1 = 3`, ...). -/

theorem andrica_iff_gapBound :
    AndricaGapBound ↔ ∀ n : ℕ, AndricaAt n :=
  ⟨fun h n => (andricaAt_iff n).mpr (h n), fun h n => (andricaAt_iff n).mp (h n)⟩

/-! ### The conditional Andrica conjecture

The Andrica conjecture is open, so what is proved here is the reduction of the
conjecture to the arithmetic gap bound `AndricaGapBound`, together with the
unconditional verification of small cases below. -/

/-- **Andrica's conjecture** (conditional on the arithmetic gap bound
`AndricaGapBound`, which is equivalent to it by `andrica_iff_gapBound`):
for every `n`, `√p_{n+1} - √p_n < 1`. -/
