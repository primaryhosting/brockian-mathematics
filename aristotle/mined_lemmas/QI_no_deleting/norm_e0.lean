/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is
-- reproduced verbatim as a module docstring immediately after the import.)
import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- A single qubit: the two-dimensional complex Hilbert space. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- Two qubits: the tensor product of two copies of `Qubit`, realized concretely as
`EuclideanSpace ℂ (Fin 2 × Fin 2)`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `a ⊗ b` of two qubit states. -/

lemma norm_e0 : ‖e0‖ = 1 := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

