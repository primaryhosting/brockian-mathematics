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

theorem pent_symm : ∀ i j : Fin 5, pent i j = pent j i := by decide

