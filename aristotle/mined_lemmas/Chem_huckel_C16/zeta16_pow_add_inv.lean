/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

lemma zeta16_pow_add_inv (m : ℕ) :
    zeta16 ^ m + (zeta16 ^ m)⁻¹ = 2 * Real.cos (2 * Real.pi * m / 16) := by
  rw [zeta16_pow_eq_exp, ← Complex.exp_neg,
    show -(((2 * Real.pi * m / 16 : ℝ) : ℂ) * Complex.I)
        = ((-(2 * Real.pi * m / 16) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

