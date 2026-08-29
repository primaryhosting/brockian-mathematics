/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

theorem zeta11_pow_add_inv (k : ℕ) :
    zeta11 ^ k + zeta11 ^ (10 * k) = ((2 * Real.cos (2 * Real.pi * k / 11) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * k / 11 with hθ
  have h1 : zeta11 ^ k = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [zeta11, ← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hprod : zeta11 ^ k * zeta11 ^ (10 * k) = 1 := by
    rw [← pow_add, show k + 10 * k = 11 * k by ring, pow_mul, zeta11_pow_eleven, one_pow]
  have h2 : zeta11 ^ (10 * k) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    have hinv : (zeta11 ^ k)⁻¹ = zeta11 ^ (10 * k) := inv_eq_of_mul_eq_one_right hprod
    rw [← hinv, h1, ← Complex.exp_neg]
    ring_nf
  rw [h1, h2, ← Complex.two_cos, Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num

