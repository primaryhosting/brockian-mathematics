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

lemma plus_apply (i : Fin 2) : plus i = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  fin_cases i <;> simp [plus, ket, EuclideanSpace.single_apply]

/-- **No-cloning theorem.**  There is no unitary `U` on `H ⊗ H` (here `H = ℂ²`,
represented as a surjective linear isometry of `H ⊗ H`) satisfying
`U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` for every state `|ψ⟩` (i.e. every unit vector).

The obstruction is linearity: cloning `|0⟩` and `|1⟩` forces `U` to send
`|+⟩ ⊗ |0⟩` to `(|00⟩ + |11⟩)/√2`, which is not `|+⟩ ⊗ |+⟩`. -/
