import Mathlib
open Matrix
namespace Frontier.PhysicsQM

theorem pauli_XY : X * Y = Complex.I • Z := by
  simp [X, Y, Z, Matrix.smul_of]
