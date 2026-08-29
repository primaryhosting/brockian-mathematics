/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
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

namespace QC

/-- The all-zeros bit string of length 8, labelling the basis state `|0…0⟩`. -/

lemma ghz8_normSq_apply (b : Fin 8 → Bool) :
    ‖ghz8.ofLp b‖ ^ 2 = (if b = allZeros then (1 / 2 : ℝ) else 0)
      + (if b = allOnes then (1 / 2 : ℝ) else 0) := by
  rw [ghz8_apply]
  by_cases h0 : b = allZeros
  · simp [h0, allZeros_ne_allOnes]
  · by_cases h1 : b = allOnes
    · simp [h1, allZeros_ne_allOnes.symm]
    · simp [h0, h1]

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
