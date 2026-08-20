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

theorem omega9_pow_nine : omega9 ^ 9 = 1 := by
  rw [omega9, ← Complex.exp_nat_mul,
    show ((9 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / 9) = 2 * (Real.pi : ℂ) * Complex.I by
      push_cast; ring]
  simp [Complex.exp_two_pi_mul_I]

