/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
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

/-- A finite set of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuple conjecture: its singular series is nonzero) when,
for every prime `p`, the elements of the set miss at least one residue class mod `p`. -/

theorem not_admissible_zero_two_four : ¬ Admissible ({0, 2, 4} : Finset ℕ) := by
  intro h
  obtain ⟨r, hr3, hr⟩ := h 3 (by norm_num)
  interval_cases r
  · exact hr 0 (by decide) rfl
  · exact hr 4 (by decide) rfl
  · exact hr 2 (by decide) rfl

/-- Extending the family: the ten-element pattern `{0, 2, 6, 8, 12, 18, 20, 26, 30, 32}`
of diameter `32`. -/
