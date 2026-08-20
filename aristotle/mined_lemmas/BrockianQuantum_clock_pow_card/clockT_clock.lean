import Mathlib
/-!
# Batch 9 — qudit generalized-Pauli extras (Weyl–Heisenberg, general d). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
variable (d : ℕ) [NeZero d]

theorem clockT_clock : (clock d)ᴴ * clock d = 1 := by
  have key : ∀ x : ZMod d, star (Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / d)) *
      Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / d) = 1 := by
    intro x
    rw [show star (Complex.exp (2 * Real.pi * Complex.I * (x.val : ℂ) / d)) =
        Complex.exp ((starRingEnd ℂ) (2 * Real.pi * Complex.I * (x.val : ℂ) / d)) from
      (Complex.exp_conj _).symm, ← Complex.exp_add]
    have hconj : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (x.val : ℂ) / d)
        = -(2 * Real.pi * Complex.I * (x.val : ℂ) / d) := by
      simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_natCast,
        map_ofNat]
      ring
    rw [hconj, neg_add_cancel, Complex.exp_zero]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, clock, Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simpa using key i
    · simp [h]
  · intro b _ hb; simp [hb]
  · intro h; simp at h

