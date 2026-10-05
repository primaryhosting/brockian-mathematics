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

@[simp] lemma v_apply (i : Fin 2) : v i = ![3 / 5, 4 / 5] i := by simp [v]

