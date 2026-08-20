import Mathlib
open Matrix
namespace Frontier.PhysicsQM

theorem pauli_sq_X : X * X = 1 := by
  simp [X, Matrix.one_fin_two]
