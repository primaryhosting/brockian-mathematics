import Mathlib
/-!
# Batch 9 — qudit generalized-Pauli extras (Weyl–Heisenberg, general d). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
variable (d : ℕ) [NeZero d]

theorem clock_diag_apply : ∀ i, clock d i i = Complex.exp (2 * Real.pi * Complex.I * (i.val : ℂ) / d) := by
  intro i; simp [clock]
end BrockianQuantum

