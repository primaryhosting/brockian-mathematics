/-
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The computational basis label `|00000⟩` of a 5-qubit register. -/

lemma norm_sq_coord (i : Fin 5 → Bool) :
    ‖ghz5.ofLp i‖ ^ 2 = (if i = allZero then (1 : ℝ) / 2 else 0)
      + (if i = allOne then (1 : ℝ) / 2 else 0) := by
  by_cases h0 : i = allZero
  · simp [ghz5, h0, allZero_ne_allOne]
  · by_cases h1 : i = allOne
    · simp [ghz5, h1, allZero_ne_allOne.symm]
    · simp [ghz5, h0, h1]

/-- The 5-qubit GHZ state is a unit vector. -/
