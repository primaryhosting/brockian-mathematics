/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, but as a plain block comment: Lean 4 forbids module
-- doc comments before `import`.)

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

namespace Brockian

/-- A finite set `H` of natural numbers is *admissible* if, for every prime `p`, the
reductions of the elements of `H` modulo `p` omit at least one residue class.
This is exactly the classical condition guaranteeing that the singular series
`𝔖(H)` attached to the tuple `H` does not vanish. -/

theorem admissible_eleven_to_twentythree : Admissible {11, 13, 17, 19, 23} := by
  refine SingularSeriesGaps7280 ?_ ?_ <;> decide

#print axioms SingularSeriesGaps7280
#print axioms exists_admissible_beyond
#print axioms admissible_eleven_to_twentythree

end Brockian

