import Mathlib
open Matrix
namespace Frontier.PhysicsQM

theorem pauli_commutator : X * Z - Z * X = (-2 * Complex.I) • Y := by
  simp [X, Y, Z, Matrix.smul_of, Complex.ext_iff]
  norm_num [Complex.I_mul_I]
  ext i
  fin_cases i
  rfl
end Frontier.PhysicsQM

