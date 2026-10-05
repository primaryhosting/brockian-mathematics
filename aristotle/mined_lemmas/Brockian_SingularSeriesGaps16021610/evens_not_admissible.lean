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

/-- `H` covers all residue classes modulo `p`. -/

private theorem evens_not_admissible : ¬ IsAdmissible evens := by
  intro hadm
  refine hadm 3 (by norm_num) ?_
  intro r hr
  interval_cases r
  · exact ⟨1602, by decide, by norm_num⟩
  · exact ⟨1606, by decide, by norm_num⟩
  · exact ⟨1604, by decide, by norm_num⟩

/-- No `5`-element subset of the gap range `[1602, 1610]` is admissible. -/
