/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- A finite set of integer shifts `H` *avoids* the prime `p` when the shifts do not cover
all residue classes modulo `p`. -/

theorem card_gapTuple16021610 : gapTuple16021610.card = 6 := by decide

/-- **Singular Series Gaps 16021610.**  The six shifts `{0, 4, 6, 10, 12, 16}` form an
admissible tuple of diameter `16`: every element lies in the gap range `[0, 16]`, the two
endpoints are attained, and for every prime `p` some residue class mod `p` is omitted, so the
associated singular series does not vanish.  For contrast, the naive tuple `{0, 2, 4}` is *not*
admissible, since it meets every residue class modulo `3`. -/
