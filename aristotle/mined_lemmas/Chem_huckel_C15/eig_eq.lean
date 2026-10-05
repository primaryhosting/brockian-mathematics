/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Matrix

/-- A primitive 15-th root of unity. -/

lemma eig_eq (k : Fin 15) : zeta ^ (k : ℕ) + zeta ^ (14 * (k : ℕ)) = eig k := by
  have hz : zeta ^ (k : ℕ) = Complex.exp (((2 * Real.pi * (k : ℕ) / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hz' : zeta ^ (14 * (k : ℕ)) =
      Complex.exp (-((2 * Real.pi * (k : ℕ) / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    have h : ((14 * (k : ℕ) : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 15)
        = -((2 * Real.pi * (k : ℕ) / 15 : ℝ) : ℂ) * Complex.I
          + ((k : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [hz, hz', ← Complex.two_cos, eig, Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num

/-- The diagonal matrix of the Hückel eigenvalues. -/
