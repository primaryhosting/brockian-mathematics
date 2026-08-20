import Mathlib
/-!
# Batch 9 — qudit generalized-Pauli extras (Weyl–Heisenberg, general d). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
variable (d : ℕ) [NeZero d]

theorem shiftT_shift : (shift d)ᴴ * shift d = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, shift, Matrix.one_apply]
  rw [Finset.sum_eq_single (i + 1)]
  · by_cases h : i = j <;> simp [h]
  · intro b _ hb; simp [hb]
  · intro h; simp at h

