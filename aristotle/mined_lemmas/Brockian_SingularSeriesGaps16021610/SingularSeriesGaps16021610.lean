/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number: `2 ≤ p` and the only divisors of `p` are `1` and `p`.
(This is the usual notion of a prime natural number.) -/

theorem SingularSeriesGaps16021610 :
    Admissible gapTuple ∧ gapTuple.length = 8 ∧ gapTuple.Nodup ∧
      0 ∈ gapTuple ∧ 26 ∈ gapTuple ∧ ∀ h ∈ gapTuple, h ≤ 26 :=
  ⟨gapTuple_admissible, by decide, by decide, by decide, by decide, by decide⟩

end Brockian

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

