import Mathlib

/-!
# Hückel theory for the cycle C₉

The adjacency matrix of the cycle graph `C₉` is diagonalized by the discrete Fourier
(Vandermonde) matrix built from a primitive 9-th root of unity.  Consequently its
characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/9))`, and its spectrum is
exactly `{2 cos (2πk/9) : k = 0, …, 8}` — the Hückel energy levels of a nine-membered
conjugated ring.
-/

open Polynomial Matrix SimpleGraph Complex

namespace Chem

/-- The adjacency matrix of the cycle graph `C₉`, over `ℂ`. -/

theorem omega9_add_pow_eight (k : Fin 9) :
    omega9 ^ (k : ℕ) + (omega9 ^ (k : ℕ)) ^ 8 = ((C9eigenvalue k : ℝ) : ℂ) := by
  have h8 : (omega9 ^ (k : ℕ)) ^ 8 = (omega9 ^ (k : ℕ))⁻¹ := by
    have hne : omega9 ≠ 0 := by simp [omega9, Complex.exp_ne_zero]
    field_simp
    linear_combination omega9_pow_pow_nine k
  have hk : omega9 ^ (k : ℕ) = Complex.exp ((2 * Real.pi * (k : ℕ) / 9 : ℝ) * Complex.I) := by
    rw [omega9, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h8, hk, ← Complex.exp_neg, C9eigenvalue]
  push_cast
  rw [Complex.two_cos]
  ring_nf

/-- The Fourier matrix diagonalizes the adjacency matrix of `C₉`. -/
