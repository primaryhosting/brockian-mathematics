import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real
open Complex Polynomial

namespace Chem

/-- A primitive 9th root of unity. -/

theorem om_pow_add_inv (k : Fin 9) : om ^ (k : ℕ) + om ^ (8 * (k : ℕ)) = lam k := by
  have hz : om ^ (k : ℕ)
      = Complex.exp (((2 * Real.pi * (k : ℕ) / 9 : ℝ) : ℂ) * Complex.I) := by
    rw [om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hmul : om ^ (k : ℕ) * om ^ (8 * (k : ℕ)) = 1 := by
    rw [← pow_add, show (k : ℕ) + 8 * (k : ℕ) = 9 * (k : ℕ) from by ring, pow_mul, om_pow_nine,
      one_pow]
  have hinv : om ^ (8 * (k : ℕ)) = (om ^ (k : ℕ))⁻¹ := (inv_eq_of_mul_eq_one_right hmul).symm
  rw [hinv, hz, ← Complex.exp_neg, lam]
  have h2 := Complex.two_cos (((2 * Real.pi * (k : ℕ) / 9 : ℝ) : ℂ))
  rw [show -(((2 * Real.pi * (k : ℕ) / 9 : ℝ) : ℂ) * Complex.I)
      = -(((2 * Real.pi * (k : ℕ) / 9 : ℝ) : ℂ)) * Complex.I from by ring, ← h2,
    Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num

