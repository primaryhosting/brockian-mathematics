import Mathlib

/-!
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace QC

/-- The state space of 4 qubits: the complex Hilbert space with orthonormal basis
indexed by bit strings `Fin 4 → Fin 2`. -/
abbrev Qubits4 : Type := EuclideanSpace ℂ (Fin 4 → Fin 2)

/-- The all-zeros bit string `0000`. -/

lemma ghz4_apply (v : Fin 4 → Fin 2) :
    ghz4.ofLp v =
      if v = allZeros then ((1 / Real.sqrt 2 : ℝ) : ℂ)
      else if v = allOnes then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0 := by
  by_cases h0 : v = allZeros
  · simp [ghz4, h0, EuclideanSpace.single_apply, allZeros_ne_allOnes]
  · by_cases h1 : v = allOnes <;>
      simp [ghz4, h0, h1, EuclideanSpace.single_apply, Ne.symm allZeros_ne_allOnes]

/-- **The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2` is a unit vector.** -/
