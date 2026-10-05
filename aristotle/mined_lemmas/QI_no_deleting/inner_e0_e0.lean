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

lemma inner_e0_e0 : (inner ℂ e0 e0 : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_e0]
  norm_num

/-- **No-deleting theorem, isometry form.** There is no linear isometry `U` of the two-qubit
space, and no fixed "blank" state, such that `U (ψ ⊗ ψ) = ψ ⊗ blank` for every unit vector
`ψ`. (No normalization of `blank` is assumed: it is forced by the hypothesis.) -/
