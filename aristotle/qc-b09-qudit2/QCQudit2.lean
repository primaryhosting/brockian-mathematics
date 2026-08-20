import Mathlib
/-!
# Batch 9 — qudit generalized-Pauli extras (Weyl–Heisenberg, general d). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
variable (d : ℕ) [NeZero d]
def shift : Matrix (ZMod d) (ZMod d) ℂ := fun i j => if i = j + 1 then 1 else 0
noncomputable def clock : Matrix (ZMod d) (ZMod d) ℂ :=
  fun i j => if i = j then Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d) else 0

theorem clock_pow_card : (clock d) ^ d = 1 := by sorry
theorem shiftT_shift : (shift d)ᴴ * shift d = 1 := by sorry
theorem clockT_clock : (clock d)ᴴ * clock d = 1 := by sorry
theorem weyl_reverse :
    shift d * clock d = Complex.exp (-(2 * Real.pi * Complex.I / d)) • (clock d * shift d) := by sorry
theorem clock_off_diag : ∀ i j, i ≠ j → clock d i j = 0 := by sorry
theorem shift_off_diag : ∀ i j, ¬ (i = j + 1) → shift d i j = 0 := by sorry
theorem clock_diag_apply : ∀ i, clock d i i = Complex.exp (2 * Real.pi * Complex.I * (i.val : ℂ) / d) := by sorry
end BrockianQuantum
