/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

lemma zeta_pow_add_inv (k : ℕ) : zeta ^ k + (zeta ^ k)⁻¹ = huckelEigenvalue k := by
  have h1 : zeta ^ k = Complex.exp (((2 * Real.pi * k / 19 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [huckelEigenvalue, h1, ← Complex.exp_neg, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- The adjacency relation of `C₁₉`. -/
