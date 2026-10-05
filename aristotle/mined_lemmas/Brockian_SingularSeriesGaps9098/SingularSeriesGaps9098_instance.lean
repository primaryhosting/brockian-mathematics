/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no imports at all), so that the
required header comment can literally be the first thing in the file.  Everything below is
built from the Lean 4 core library only.
-/

namespace Brockian

/-! ## Primality, admissible gap patterns -/

/-- Primality, spelled out from first principles: `p` is at least `2` and its only divisors
are `1` and `p`. -/

theorem SingularSeriesGaps9098_instance :
    Admissible (gapPattern 9098 (fact 9098)) :=
  admissible_gapPattern_fact 9098

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

