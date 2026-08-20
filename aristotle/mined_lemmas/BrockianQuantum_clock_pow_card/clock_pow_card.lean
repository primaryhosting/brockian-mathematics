import Mathlib
/-!
# Batch 9 — qudit generalized-Pauli extras (Weyl–Heisenberg, general d). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
variable (d : ℕ) [NeZero d]

theorem clock_pow_card : (clock d) ^ d = 1 := by
  have hdiag : clock d = Matrix.diagonal
      (fun j : ZMod d => Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / d)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [clock, Matrix.diagonal]
    · simp [clock, Matrix.diagonal, h]
  rw [hdiag, Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext j
  rw [Pi.pow_apply, ← Complex.exp_nat_mul]
  have h : (d : ℂ) * (2 * Real.pi * Complex.I * (j.val : ℂ) / d)
      = (j.val : ℤ) * (2 * Real.pi * Complex.I) := by
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
    field_simp
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

