import Mathlib

/-!
# Singular Series Gaps 13501360
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps13501360
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

set_option grind.warning false

namespace Brockian

/-- The set of residue classes modulo `p` occupied by the tuple `H`. -/

theorem SingularSeriesGaps13501360_instance :
    Admissible (gapTuple 13501360 30030 13) ∧
      ∀ p : ℕ, p.Prime → 0 < 1 - (localCount (gapTuple 13501360 30030 13) p : ℝ) / p := by
  refine SingularSeriesGaps13501360 13501360 30030 13 (by norm_num) ?_
  intro p hp hple
  interval_cases p <;> revert hp <;> decide

end Brockian

