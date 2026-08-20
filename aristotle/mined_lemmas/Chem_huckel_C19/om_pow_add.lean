/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma om_pow_add (m : ℕ) :
    om ^ m + om ^ (18 * m) = 2 * (Real.cos (2 * Real.pi * m / 19) : ℝ) := by
  have key : ((2 * Real.pi * ((18 * m : ℕ) : ℝ) / 19 : ℝ) : ℂ) * Complex.I
      = (2 * Real.pi * m : ℂ) * Complex.I + ((-(2 * Real.pi * m / 19 : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  have h1 : om ^ (18 * m) = Complex.exp ((-(2 * Real.pi * m / 19 : ℝ) : ℂ) * Complex.I) := by
    rw [om_pow_eq_exp, key, Complex.exp_add, exp_two_pi_nat, one_mul]
  rw [om_pow_eq_exp, h1, Complex.ofReal_cos, Complex.two_cos]

/-! ### The Fourier matrix diagonalises the adjacency matrix -/

