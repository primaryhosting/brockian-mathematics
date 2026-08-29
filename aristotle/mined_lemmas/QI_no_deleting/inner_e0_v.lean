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

lemma inner_e0_v : (inner ℂ e0 v : ℂ) = 3 / 5 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]

