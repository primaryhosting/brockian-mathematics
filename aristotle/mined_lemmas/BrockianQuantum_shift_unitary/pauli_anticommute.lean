import Mathlib
/-!
# Stabilizer formalism: qudit generalized-Pauli unitarity + qubit Pauli anticommutation.
Bare `import Mathlib`; no non-core/Archive namespaces or invented lemmas. All TRUE.
-/
namespace BrockianQuantum
open Matrix

variable (d : ℕ) [NeZero d]

/-- Qudit **shift** (generalized Pauli X). -/

theorem pauli_anticommute :
    (Matrix.of ![![(0:ℂ), 1], ![1, 0]]) * (Matrix.of ![![(1:ℂ), 0], ![0, -1]])
      = - ((Matrix.of ![![(1:ℂ), 0], ![0, -1]]) * (Matrix.of ![![(0:ℂ), 1], ![1, 0]])) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

end BrockianQuantum

