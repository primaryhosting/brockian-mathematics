/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Pigeonhole for five two-valued items: among five booleans, some three of them
(at three distinct positions) are equal. -/

theorem pigeon_five (a b c d e : Bool) :
    (a = b ∧ b = c) ∨ (a = b ∧ b = d) ∨ (a = b ∧ b = e) ∨
    (a = c ∧ c = d) ∨ (a = c ∧ c = e) ∨ (a = d ∧ d = e) ∨
    (b = c ∧ c = d) ∨ (b = c ∧ c = e) ∨ (b = d ∧ d = e) ∨
    (c = d ∧ d = e) := by
  decide +revert

/-- The core step of the Ramsey argument: if the three edges from the vertex `0`
to three further distinct vertices `p`, `q`, `r` all have the same colour, then a
monochromatic triangle exists (either using `0`, or the triangle `p q r`). -/
