import Mathlib
/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma exp_add_inv (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) + (Complex.exp ((x : ℂ) * Complex.I))⁻¹
      = 2 * (Real.cos x : ℂ) := by
  rw [← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    show ((-(x : ℂ))) = ((-x : ℝ) : ℂ) by push_cast; ring]
  simp [Complex.ofReal_cos]
  ring

/-- The `k`-th eigenvalue expressed via the root of unity. -/
