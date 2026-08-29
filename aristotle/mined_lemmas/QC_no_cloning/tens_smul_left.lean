/-
/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: verified (axioms: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace QC

/-- The qubit Hilbert space `H = ℂ²`. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `H ⊗ H`, realized concretely as `ℂ^(2×2)`. -/
abbrev QubitPair := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The computational basis states `|0⟩` and `|1⟩`. -/

lemma tens_smul_left (r : ℂ) (a c : Qubit) : tens (r • a) c = r • tens a c := by
  ext p; simp [mul_assoc]

/-- The uniform superposition `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
