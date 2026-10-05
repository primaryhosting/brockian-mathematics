/-!
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- `IsPrime p` : `p` is at least `2` and has no divisor `d` with `2 ≤ d < p`. -/

theorem pick_of_two (A B : Int) :
    ((1 : Int) ≠ A ∧ (1 : Int) ≠ B) ∨ ((2 : Int) ≠ A ∧ (2 : Int) ≠ B) ∨
      ((3 : Int) ≠ A ∧ (3 : Int) ≠ B) := by omega

