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
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Gaps 12401250
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps12401250
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

/-- A finite set `H` of natural numbers is *admissible* (in the sense of the
Hardy–Littlewood prime `k`-tuples conjecture) if for every prime `p` the residues
of the elements of `H` modulo `p` do not cover all of `ZMod p`. -/

theorem singularSeries_factor_pos_gapTuple (n : ℕ) (hn : n = 1242 ∨ n = 1246)
    (p : ℕ) (hp : p.Prime) : 0 < 1 - (localCount (gapTuple n) p : ℝ) / p := by
  rcases hn with rfl | rfl
  · exact singularSeries_factor_pos admissible_gapTuple_1242 p hp
  · exact singularSeries_factor_pos admissible_gapTuple_1246 p hp

end Brockian

