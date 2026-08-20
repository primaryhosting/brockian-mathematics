import Mathlib
/-!
# Batch 9 — qudit generalized-Pauli extras (Weyl–Heisenberg, general d). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
variable (d : ℕ) [NeZero d]

theorem clock_off_diag : ∀ i j, i ≠ j → clock d i j = 0 := by
  intro i j h; simp [clock, h]

