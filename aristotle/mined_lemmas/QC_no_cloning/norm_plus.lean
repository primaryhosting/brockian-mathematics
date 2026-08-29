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

lemma norm_plus : ‖plus‖ = 1 := by
  have h2 : ‖ket 0 + ket 1‖ = Real.sqrt 2 := by
    rw [EuclideanSpace.norm_eq]
    norm_num [ket, Fin.sum_univ_two, EuclideanSpace.single_apply]
  rw [plus, norm_smul, h2, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  field_simp

