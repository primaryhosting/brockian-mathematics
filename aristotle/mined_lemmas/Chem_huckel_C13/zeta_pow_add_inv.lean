/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Chem

/-! ### The cyclic shift operator -/

/-- The cyclic shift endomorphism of `Fin 13 → ℂ`, `f ↦ (i ↦ f (i + 1))`. -/

lemma zeta_pow_add_inv (k : ℕ) :
    zeta ^ k + (zeta ^ k)⁻¹ = 2 * (Real.cos (2 * Real.pi * k / 13) : ℂ) := by
  have hz : zeta ^ k = Complex.exp (((2 * Real.pi * k / 13 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hz, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-! ### The characteristic factorisation -/

/-- The polynomial whose roots are the claimed eigenvalues. -/
